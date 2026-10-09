import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0313 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0313 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0313 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0313_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61263360 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314 : SparsePolynomial.Poly := [([2,5,9], 1)]
theorem eval_atom0314 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0314 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0314_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102746880 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315 : SparsePolynomial.Poly := [([2,5,10], 1)]
theorem eval_atom0315 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0315 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0315_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68907600 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316 : SparsePolynomial.Poly := [([2,5,11], 1)]
theorem eval_atom0316 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0316 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0316_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86732640 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317 : SparsePolynomial.Poly := [([2,5,12], 1)]
theorem eval_atom0317 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0317 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0317_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (84196080 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318 : SparsePolynomial.Poly := [([2,5,13], 1)]
theorem eval_atom0318 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0318 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0318_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (87441840 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319 : SparsePolynomial.Poly := [([2,5,14], 1)]
theorem eval_atom0319 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0319 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0319_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (113022000 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0320 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0320 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0320_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38949120 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0321 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0321 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0321_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76222080 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0322 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0322 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0322_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74545920 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0323 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0323 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0323_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108552960 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0324 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0324 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0324_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81308880 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0325 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0325 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0325_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99692640 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326 : SparsePolynomial.Poly := [([2,6,12], 1)]
theorem eval_atom0326 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0326 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0326_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98187120 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327 : SparsePolynomial.Poly := [([2,6,13], 1)]
theorem eval_atom0327 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0327 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0327_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103051440 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328 : SparsePolynomial.Poly := [([2,6,14], 1)]
theorem eval_atom0328 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0328 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0328_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130250160 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0329 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0329 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0329_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47187840 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0330 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0330 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0330_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (89790720 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0331 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0331 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0331_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116319360 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0332 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0332 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0332_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (92273280 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0333 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0333 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0333_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112652640 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334 : SparsePolynomial.Poly := [([2,7,12], 1)]
theorem eval_atom0334 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0334 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0334_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (106327680 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335 : SparsePolynomial.Poly := [([2,7,13], 1)]
theorem eval_atom0335 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0335 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0335_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110265600 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336 : SparsePolynomial.Poly := [([2,7,14], 1)]
theorem eval_atom0336 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0336 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0336_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136537920 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0337 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0337 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0337_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54432000 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0338 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0338 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0338_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (131245920 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0339 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0339 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0339_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102967200 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0340 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0340 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0340_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125612640 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0341 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0341 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0341_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (117365760 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0342 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0342 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0342_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (107917920 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0343 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0343 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0343_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (160228800 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0344 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0344 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0344_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90201600 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0345 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0345 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0345_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146759040 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0346 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0346 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0346_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193004640 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0347 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0347 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0347_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188334720 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0348 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0348 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0348_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110393280 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0349 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0349 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0349_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (182864520 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0350 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0350 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0350_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (67526784 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0351 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0351 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0351_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158776200 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0352 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0352 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0352_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177655680 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353 : SparsePolynomial.Poly := [([2,10,13], 1)]
theorem eval_atom0353 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0353 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0353_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120372480 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354 : SparsePolynomial.Poly := [([2,10,14], 1)]
theorem eval_atom0354 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0354 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0354_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150013080 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0355 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0355 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0355_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102218760 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356 : SparsePolynomial.Poly := [([2,11,12], 1)]
theorem eval_atom0356 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0356 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0356_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (172461960 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357 : SparsePolynomial.Poly := [([2,11,13], 1)]
theorem eval_atom0357 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0357 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0357_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (115864560 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358 : SparsePolynomial.Poly := [([2,11,14], 1)]
theorem eval_atom0358 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0358 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0358_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (154996200 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359 : SparsePolynomial.Poly := [([2,12,12], 1)]
theorem eval_atom0359 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0359 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0359_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64540800 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360 : SparsePolynomial.Poly := [([2,12,13], 1)]
theorem eval_atom0360 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0360 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0360_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90966240 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361 : SparsePolynomial.Poly := [([2,12,14], 1)]
theorem eval_atom0361 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0361 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0361_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136631880 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362 : SparsePolynomial.Poly := [([2,13,13], 1)]
theorem eval_atom0362 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0362 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0362_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15655680 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363 : SparsePolynomial.Poly := [([2,13,14], 1)]
theorem eval_atom0363 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0363 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0363_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78867000 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364 : SparsePolynomial.Poly := [([2,14,14], 1)]
theorem eval_atom0364 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0364 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0364_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55821960 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0365 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0365 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0365_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1382400 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0366 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0366 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0366_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (898560 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0367 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0367 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0367_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (449280 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom0368 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0368 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0368_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25693200 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369 : SparsePolynomial.Poly := [([3,3,11], 1)]
theorem eval_atom0369 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0369 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0369_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9257760 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0370 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0370 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0370_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4746240 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0371 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0371 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0371_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2148480 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0372 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0372 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0372_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3600000 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0373 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0373 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0373_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5500800 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0374 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0374 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0374_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7401600 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom0375 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0375 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0375_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56678400 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom0376 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0376 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0376_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16715520 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom0377 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0377 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0377_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35445600 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom0378 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0378 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0378_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31541760 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom0379 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0379 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0379_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40792320 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom0380 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0380 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0380_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50042880 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0381 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0381 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0381_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8098560 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0382 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0382 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0382_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16456320 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0383 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0383 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0383_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19065600 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0384 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0384 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0384_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21674880 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom0385 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0385 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0385_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64419840 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom0386 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0386 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0386_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35062560 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom0387 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0387 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0387_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52725600 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388 : SparsePolynomial.Poly := [([3,5,12], 1)]
theorem eval_atom0388 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0388 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0388_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56619360 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389 : SparsePolynomial.Poly := [([3,5,13], 1)]
theorem eval_atom0389 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0389 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0389_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70120800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390 : SparsePolynomial.Poly := [([3,5,14], 1)]
theorem eval_atom0390 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0390 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0390_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83622240 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0391 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0391 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0391_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15724800 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0392 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0392 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0392_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33575040 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block004 : SparsePolynomial.Poly := [([2,5,8], 61263360), ([2,5,9], 102746880), ([2,5,10], 68907600), ([2,5,11], 86732640), ([2,5,12], 84196080), ([2,5,13], 87441840), ([2,5,14], 113022000), ([2,6,6], 38949120), ([2,6,7], 76222080), ([2,6,8], 74545920), ([2,6,9], 108552960), ([2,6,10], 81308880), ([2,6,11], 99692640), ([2,6,12], 98187120), ([2,6,13], 103051440), ([2,6,14], 130250160), ([2,7,7], 47187840), ([2,7,8], 89790720), ([2,7,9], 116319360), ([2,7,10], 92273280), ([2,7,11], 112652640), ([2,7,12], 106327680), ([2,7,13], 110265600), ([2,7,14], 136537920), ([2,8,8], 54432000), ([2,8,9], 131245920), ([2,8,10], 102967200), ([2,8,11], 125612640), ([2,8,12], 117365760), ([2,8,13], 107917920), ([2,8,14], 160228800), ([2,9,9], 90201600), ([2,9,10], 146759040), ([2,9,11], 193004640), ([2,9,12], 188334720), ([2,9,13], 110393280), ([2,9,14], 182864520), ([2,10,10], 67526784), ([2,10,11], 158776200), ([2,10,12], 177655680), ([2,10,13], 120372480), ([2,10,14], 150013080), ([2,11,11], 102218760), ([2,11,12], 172461960), ([2,11,13], 115864560), ([2,11,14], 154996200), ([2,12,12], 64540800), ([2,12,13], 90966240), ([2,12,14], 136631880), ([2,13,13], 15655680), ([2,13,14], 78867000), ([2,14,14], 55821960), ([3,3,3], 1382400), ([3,3,4], 898560), ([3,3,5], 449280), ([3,3,9], 25693200), ([3,3,11], 9257760), ([3,4,4], 4746240), ([3,4,5], 2148480), ([3,4,6], 3600000), ([3,4,7], 5500800), ([3,4,8], 7401600), ([3,4,9], 56678400), ([3,4,10], 16715520), ([3,4,11], 35445600), ([3,4,12], 31541760), ([3,4,13], 40792320), ([3,4,14], 50042880), ([3,5,5], 8098560), ([3,5,6], 16456320), ([3,5,7], 19065600), ([3,5,8], 21674880), ([3,5,9], 64419840), ([3,5,10], 35062560), ([3,5,11], 52725600), ([3,5,12], 56619360), ([3,5,13], 70120800), ([3,5,14], 83622240), ([3,6,6], 15724800), ([3,6,7], 33575040)]
theorem block004_data : block004 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (61263360 : Int) atom0313) (SparsePolynomial.scale (102746880 : Int) atom0314)) (SparsePolynomial.merge (SparsePolynomial.scale (68907600 : Int) atom0315) (SparsePolynomial.merge (SparsePolynomial.scale (86732640 : Int) atom0316) (SparsePolynomial.scale (84196080 : Int) atom0317)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (87441840 : Int) atom0318) (SparsePolynomial.scale (113022000 : Int) atom0319)) (SparsePolynomial.merge (SparsePolynomial.scale (38949120 : Int) atom0320) (SparsePolynomial.merge (SparsePolynomial.scale (76222080 : Int) atom0321) (SparsePolynomial.scale (74545920 : Int) atom0322))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (108552960 : Int) atom0323) (SparsePolynomial.scale (81308880 : Int) atom0324)) (SparsePolynomial.merge (SparsePolynomial.scale (99692640 : Int) atom0325) (SparsePolynomial.merge (SparsePolynomial.scale (98187120 : Int) atom0326) (SparsePolynomial.scale (103051440 : Int) atom0327)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (130250160 : Int) atom0328) (SparsePolynomial.scale (47187840 : Int) atom0329)) (SparsePolynomial.merge (SparsePolynomial.scale (89790720 : Int) atom0330) (SparsePolynomial.merge (SparsePolynomial.scale (116319360 : Int) atom0331) (SparsePolynomial.scale (92273280 : Int) atom0332)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (112652640 : Int) atom0333) (SparsePolynomial.scale (106327680 : Int) atom0334)) (SparsePolynomial.merge (SparsePolynomial.scale (110265600 : Int) atom0335) (SparsePolynomial.merge (SparsePolynomial.scale (136537920 : Int) atom0336) (SparsePolynomial.scale (54432000 : Int) atom0337)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (131245920 : Int) atom0338) (SparsePolynomial.scale (102967200 : Int) atom0339)) (SparsePolynomial.merge (SparsePolynomial.scale (125612640 : Int) atom0340) (SparsePolynomial.merge (SparsePolynomial.scale (117365760 : Int) atom0341) (SparsePolynomial.scale (107917920 : Int) atom0342))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (160228800 : Int) atom0343) (SparsePolynomial.scale (90201600 : Int) atom0344)) (SparsePolynomial.merge (SparsePolynomial.scale (146759040 : Int) atom0345) (SparsePolynomial.merge (SparsePolynomial.scale (193004640 : Int) atom0346) (SparsePolynomial.scale (188334720 : Int) atom0347)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (110393280 : Int) atom0348) (SparsePolynomial.scale (182864520 : Int) atom0349)) (SparsePolynomial.merge (SparsePolynomial.scale (67526784 : Int) atom0350) (SparsePolynomial.merge (SparsePolynomial.scale (158776200 : Int) atom0351) (SparsePolynomial.scale (177655680 : Int) atom0352))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (120372480 : Int) atom0353) (SparsePolynomial.scale (150013080 : Int) atom0354)) (SparsePolynomial.merge (SparsePolynomial.scale (102218760 : Int) atom0355) (SparsePolynomial.merge (SparsePolynomial.scale (172461960 : Int) atom0356) (SparsePolynomial.scale (115864560 : Int) atom0357)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (154996200 : Int) atom0358) (SparsePolynomial.scale (64540800 : Int) atom0359)) (SparsePolynomial.merge (SparsePolynomial.scale (90966240 : Int) atom0360) (SparsePolynomial.merge (SparsePolynomial.scale (136631880 : Int) atom0361) (SparsePolynomial.scale (15655680 : Int) atom0362))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (78867000 : Int) atom0363) (SparsePolynomial.scale (55821960 : Int) atom0364)) (SparsePolynomial.merge (SparsePolynomial.scale (1382400 : Int) atom0365) (SparsePolynomial.merge (SparsePolynomial.scale (898560 : Int) atom0366) (SparsePolynomial.scale (449280 : Int) atom0367)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25693200 : Int) atom0368) (SparsePolynomial.scale (9257760 : Int) atom0369)) (SparsePolynomial.merge (SparsePolynomial.scale (4746240 : Int) atom0370) (SparsePolynomial.merge (SparsePolynomial.scale (2148480 : Int) atom0371) (SparsePolynomial.scale (3600000 : Int) atom0372)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5500800 : Int) atom0373) (SparsePolynomial.scale (7401600 : Int) atom0374)) (SparsePolynomial.merge (SparsePolynomial.scale (56678400 : Int) atom0375) (SparsePolynomial.merge (SparsePolynomial.scale (16715520 : Int) atom0376) (SparsePolynomial.scale (35445600 : Int) atom0377)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31541760 : Int) atom0378) (SparsePolynomial.scale (40792320 : Int) atom0379)) (SparsePolynomial.merge (SparsePolynomial.scale (50042880 : Int) atom0380) (SparsePolynomial.merge (SparsePolynomial.scale (8098560 : Int) atom0381) (SparsePolynomial.scale (16456320 : Int) atom0382))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19065600 : Int) atom0383) (SparsePolynomial.scale (21674880 : Int) atom0384)) (SparsePolynomial.merge (SparsePolynomial.scale (64419840 : Int) atom0385) (SparsePolynomial.merge (SparsePolynomial.scale (35062560 : Int) atom0386) (SparsePolynomial.scale (52725600 : Int) atom0387)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (56619360 : Int) atom0388) (SparsePolynomial.scale (70120800 : Int) atom0389)) (SparsePolynomial.merge (SparsePolynomial.scale (83622240 : Int) atom0390) (SparsePolynomial.merge (SparsePolynomial.scale (15724800 : Int) atom0391) (SparsePolynomial.scale (33575040 : Int) atom0392)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block004 := by
  rw [block004_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0313_nonneg g hg hA hB) (atom0314_nonneg g hg hA hB)) (add_nonneg (atom0315_nonneg g hg hA hB) (add_nonneg (atom0316_nonneg g hg hA hB) (atom0317_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0318_nonneg g hg hA hB) (atom0319_nonneg g hg hA hB)) (add_nonneg (atom0320_nonneg g hg hA hB) (add_nonneg (atom0321_nonneg g hg hA hB) (atom0322_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0323_nonneg g hg hA hB) (atom0324_nonneg g hg hA hB)) (add_nonneg (atom0325_nonneg g hg hA hB) (add_nonneg (atom0326_nonneg g hg hA hB) (atom0327_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0328_nonneg g hg hA hB) (atom0329_nonneg g hg hA hB)) (add_nonneg (atom0330_nonneg g hg hA hB) (add_nonneg (atom0331_nonneg g hg hA hB) (atom0332_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0333_nonneg g hg hA hB) (atom0334_nonneg g hg hA hB)) (add_nonneg (atom0335_nonneg g hg hA hB) (add_nonneg (atom0336_nonneg g hg hA hB) (atom0337_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0338_nonneg g hg hA hB) (atom0339_nonneg g hg hA hB)) (add_nonneg (atom0340_nonneg g hg hA hB) (add_nonneg (atom0341_nonneg g hg hA hB) (atom0342_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0343_nonneg g hg hA hB) (atom0344_nonneg g hg hA hB)) (add_nonneg (atom0345_nonneg g hg hA hB) (add_nonneg (atom0346_nonneg g hg hA hB) (atom0347_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0348_nonneg g hg hA hB) (atom0349_nonneg g hg hA hB)) (add_nonneg (atom0350_nonneg g hg hA hB) (add_nonneg (atom0351_nonneg g hg hA hB) (atom0352_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0353_nonneg g hg hA hB) (atom0354_nonneg g hg hA hB)) (add_nonneg (atom0355_nonneg g hg hA hB) (add_nonneg (atom0356_nonneg g hg hA hB) (atom0357_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0358_nonneg g hg hA hB) (atom0359_nonneg g hg hA hB)) (add_nonneg (atom0360_nonneg g hg hA hB) (add_nonneg (atom0361_nonneg g hg hA hB) (atom0362_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0363_nonneg g hg hA hB) (atom0364_nonneg g hg hA hB)) (add_nonneg (atom0365_nonneg g hg hA hB) (add_nonneg (atom0366_nonneg g hg hA hB) (atom0367_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0368_nonneg g hg hA hB) (atom0369_nonneg g hg hA hB)) (add_nonneg (atom0370_nonneg g hg hA hB) (add_nonneg (atom0371_nonneg g hg hA hB) (atom0372_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0373_nonneg g hg hA hB) (atom0374_nonneg g hg hA hB)) (add_nonneg (atom0375_nonneg g hg hA hB) (add_nonneg (atom0376_nonneg g hg hA hB) (atom0377_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0378_nonneg g hg hA hB) (atom0379_nonneg g hg hA hB)) (add_nonneg (atom0380_nonneg g hg hA hB) (add_nonneg (atom0381_nonneg g hg hA hB) (atom0382_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0383_nonneg g hg hA hB) (atom0384_nonneg g hg hA hB)) (add_nonneg (atom0385_nonneg g hg hA hB) (add_nonneg (atom0386_nonneg g hg hA hB) (atom0387_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0388_nonneg g hg hA hB) (atom0389_nonneg g hg hA hB)) (add_nonneg (atom0390_nonneg g hg hA hB) (add_nonneg (atom0391_nonneg g hg hA hB) (atom0392_nonneg g hg hA hB))))))))

end APPT.Finite15
