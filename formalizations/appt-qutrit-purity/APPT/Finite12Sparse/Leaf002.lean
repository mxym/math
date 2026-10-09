import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0160 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0160 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167040 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0161 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223104 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0162 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231552 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0163 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122400 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0164 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225744 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0165 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79488 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0166 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181440 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0167 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223488 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0168 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150336 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0169 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195312 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0170 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119808 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0171 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214272 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0172 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152160 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0173 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213168 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0174 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84672 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0175 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135504 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0176 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208848 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0177 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35712 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0178 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152808 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0179 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106704 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0180 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4608 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0181 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36672 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0182 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0183 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10656 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom0184 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1584 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185 : SparsePolynomial.Poly := [([3,3,11], 1)]
theorem eval_atom0185 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1680 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0186 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2112 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0187 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69696 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0188 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20352 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0189 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53184 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom0190 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48288 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom0191 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60528 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom0192 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86640 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0193 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10368 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0194 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72960 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0195 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46848 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0196 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83712 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom0197 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91392 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom0198 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102000 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom0199 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154368 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0200 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77184 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0201 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121344 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0202 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188160 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203 : SparsePolynomial.Poly := [([3,6,9], 1)]
theorem eval_atom0203 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207360 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204 : SparsePolynomial.Poly := [([3,6,10], 1)]
theorem eval_atom0204 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115800 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205 : SparsePolynomial.Poly := [([3,6,11], 1)]
theorem eval_atom0205 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217344 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0206 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58752 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0207 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153600 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208 : SparsePolynomial.Poly := [([3,7,9], 1)]
theorem eval_atom0208 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (209280 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209 : SparsePolynomial.Poly := [([3,7,10], 1)]
theorem eval_atom0209 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149760 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210 : SparsePolynomial.Poly := [([3,7,11], 1)]
theorem eval_atom0210 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204288 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0211 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109440 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212 : SparsePolynomial.Poly := [([3,8,9], 1)]
theorem eval_atom0212 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210048 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213 : SparsePolynomial.Poly := [([3,8,10], 1)]
theorem eval_atom0213 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157608 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214 : SparsePolynomial.Poly := [([3,8,11], 1)]
theorem eval_atom0214 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241152 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom0215 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87552 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216 : SparsePolynomial.Poly := [([3,9,10], 1)]
theorem eval_atom0216 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150396 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217 : SparsePolynomial.Poly := [([3,9,11], 1)]
theorem eval_atom0217 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254208 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom0218 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41040 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219 : SparsePolynomial.Poly := [([3,10,11], 1)]
theorem eval_atom0219 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201786 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom0220 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152064 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0221 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (384 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0222 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21696 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0223 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5568 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224 : SparsePolynomial.Poly := [([4,4,9], 1)]
theorem eval_atom0224 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1152 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225 : SparsePolynomial.Poly := [([4,4,11], 1)]
theorem eval_atom0225 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6144 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0226 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3840 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0227 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28320 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228 : SparsePolynomial.Poly := [([4,5,7], 1)]
theorem eval_atom0228 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5760 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229 : SparsePolynomial.Poly := [([4,5,8], 1)]
theorem eval_atom0229 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28512 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230 : SparsePolynomial.Poly := [([4,5,9], 1)]
theorem eval_atom0230 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37488 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom0231 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48768 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom0232 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106344 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0233 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48960 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0234 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80064 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0235 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153216 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom0236 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183168 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom0237 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102048 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom0238 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214656 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0239 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38016 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block002 : SparsePolynomial.Poly := [([2,6,7], 167040), ([2,6,8], 223104), ([2,6,9], 231552), ([2,6,10], 122400), ([2,6,11], 225744), ([2,7,7], 79488), ([2,7,8], 181440), ([2,7,9], 223488), ([2,7,10], 150336), ([2,7,11], 195312), ([2,8,8], 119808), ([2,8,9], 214272), ([2,8,10], 152160), ([2,8,11], 213168), ([2,9,9], 84672), ([2,9,10], 135504), ([2,9,11], 208848), ([2,10,10], 35712), ([2,10,11], 152808), ([2,11,11], 106704), ([3,3,3], 4608), ([3,3,6], 36672), ([3,3,7], 96), ([3,3,8], 10656), ([3,3,9], 1584), ([3,3,11], 1680), ([3,4,5], 2112), ([3,4,6], 69696), ([3,4,7], 20352), ([3,4,8], 53184), ([3,4,9], 48288), ([3,4,10], 60528), ([3,4,11], 86640), ([3,5,5], 10368), ([3,5,6], 72960), ([3,5,7], 46848), ([3,5,8], 83712), ([3,5,9], 91392), ([3,5,10], 102000), ([3,5,11], 154368), ([3,6,6], 77184), ([3,6,7], 121344), ([3,6,8], 188160), ([3,6,9], 207360), ([3,6,10], 115800), ([3,6,11], 217344), ([3,7,7], 58752), ([3,7,8], 153600), ([3,7,9], 209280), ([3,7,10], 149760), ([3,7,11], 204288), ([3,8,8], 109440), ([3,8,9], 210048), ([3,8,10], 157608), ([3,8,11], 241152), ([3,9,9], 87552), ([3,9,10], 150396), ([3,9,11], 254208), ([3,10,10], 41040), ([3,10,11], 201786), ([3,11,11], 152064), ([4,4,4], 384), ([4,4,6], 21696), ([4,4,8], 5568), ([4,4,9], 1152), ([4,4,11], 6144), ([4,5,5], 3840), ([4,5,6], 28320), ([4,5,7], 5760), ([4,5,8], 28512), ([4,5,9], 37488), ([4,5,10], 48768), ([4,5,11], 106344), ([4,6,6], 48960), ([4,6,7], 80064), ([4,6,8], 153216), ([4,6,9], 183168), ([4,6,10], 102048), ([4,6,11], 214656), ([4,7,7], 38016)]
theorem block002_data : block002 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (167040 : Int) atom0160) (SparsePolynomial.scale (223104 : Int) atom0161)) (SparsePolynomial.merge (SparsePolynomial.scale (231552 : Int) atom0162) (SparsePolynomial.merge (SparsePolynomial.scale (122400 : Int) atom0163) (SparsePolynomial.scale (225744 : Int) atom0164)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (79488 : Int) atom0165) (SparsePolynomial.scale (181440 : Int) atom0166)) (SparsePolynomial.merge (SparsePolynomial.scale (223488 : Int) atom0167) (SparsePolynomial.merge (SparsePolynomial.scale (150336 : Int) atom0168) (SparsePolynomial.scale (195312 : Int) atom0169))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (119808 : Int) atom0170) (SparsePolynomial.scale (214272 : Int) atom0171)) (SparsePolynomial.merge (SparsePolynomial.scale (152160 : Int) atom0172) (SparsePolynomial.merge (SparsePolynomial.scale (213168 : Int) atom0173) (SparsePolynomial.scale (84672 : Int) atom0174)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (135504 : Int) atom0175) (SparsePolynomial.scale (208848 : Int) atom0176)) (SparsePolynomial.merge (SparsePolynomial.scale (35712 : Int) atom0177) (SparsePolynomial.merge (SparsePolynomial.scale (152808 : Int) atom0178) (SparsePolynomial.scale (106704 : Int) atom0179)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4608 : Int) atom0180) (SparsePolynomial.scale (36672 : Int) atom0181)) (SparsePolynomial.merge (SparsePolynomial.scale (96 : Int) atom0182) (SparsePolynomial.merge (SparsePolynomial.scale (10656 : Int) atom0183) (SparsePolynomial.scale (1584 : Int) atom0184)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1680 : Int) atom0185) (SparsePolynomial.scale (2112 : Int) atom0186)) (SparsePolynomial.merge (SparsePolynomial.scale (69696 : Int) atom0187) (SparsePolynomial.merge (SparsePolynomial.scale (20352 : Int) atom0188) (SparsePolynomial.scale (53184 : Int) atom0189))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48288 : Int) atom0190) (SparsePolynomial.scale (60528 : Int) atom0191)) (SparsePolynomial.merge (SparsePolynomial.scale (86640 : Int) atom0192) (SparsePolynomial.merge (SparsePolynomial.scale (10368 : Int) atom0193) (SparsePolynomial.scale (72960 : Int) atom0194)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46848 : Int) atom0195) (SparsePolynomial.scale (83712 : Int) atom0196)) (SparsePolynomial.merge (SparsePolynomial.scale (91392 : Int) atom0197) (SparsePolynomial.merge (SparsePolynomial.scale (102000 : Int) atom0198) (SparsePolynomial.scale (154368 : Int) atom0199))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (77184 : Int) atom0200) (SparsePolynomial.scale (121344 : Int) atom0201)) (SparsePolynomial.merge (SparsePolynomial.scale (188160 : Int) atom0202) (SparsePolynomial.merge (SparsePolynomial.scale (207360 : Int) atom0203) (SparsePolynomial.scale (115800 : Int) atom0204)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (217344 : Int) atom0205) (SparsePolynomial.scale (58752 : Int) atom0206)) (SparsePolynomial.merge (SparsePolynomial.scale (153600 : Int) atom0207) (SparsePolynomial.merge (SparsePolynomial.scale (209280 : Int) atom0208) (SparsePolynomial.scale (149760 : Int) atom0209))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (204288 : Int) atom0210) (SparsePolynomial.scale (109440 : Int) atom0211)) (SparsePolynomial.merge (SparsePolynomial.scale (210048 : Int) atom0212) (SparsePolynomial.merge (SparsePolynomial.scale (157608 : Int) atom0213) (SparsePolynomial.scale (241152 : Int) atom0214)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (87552 : Int) atom0215) (SparsePolynomial.scale (150396 : Int) atom0216)) (SparsePolynomial.merge (SparsePolynomial.scale (254208 : Int) atom0217) (SparsePolynomial.merge (SparsePolynomial.scale (41040 : Int) atom0218) (SparsePolynomial.scale (201786 : Int) atom0219)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (152064 : Int) atom0220) (SparsePolynomial.scale (384 : Int) atom0221)) (SparsePolynomial.merge (SparsePolynomial.scale (21696 : Int) atom0222) (SparsePolynomial.merge (SparsePolynomial.scale (5568 : Int) atom0223) (SparsePolynomial.scale (1152 : Int) atom0224)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6144 : Int) atom0225) (SparsePolynomial.scale (3840 : Int) atom0226)) (SparsePolynomial.merge (SparsePolynomial.scale (28320 : Int) atom0227) (SparsePolynomial.merge (SparsePolynomial.scale (5760 : Int) atom0228) (SparsePolynomial.scale (28512 : Int) atom0229))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37488 : Int) atom0230) (SparsePolynomial.scale (48768 : Int) atom0231)) (SparsePolynomial.merge (SparsePolynomial.scale (106344 : Int) atom0232) (SparsePolynomial.merge (SparsePolynomial.scale (48960 : Int) atom0233) (SparsePolynomial.scale (80064 : Int) atom0234)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (153216 : Int) atom0235) (SparsePolynomial.scale (183168 : Int) atom0236)) (SparsePolynomial.merge (SparsePolynomial.scale (102048 : Int) atom0237) (SparsePolynomial.merge (SparsePolynomial.scale (214656 : Int) atom0238) (SparsePolynomial.scale (38016 : Int) atom0239)))))))) := by decide +kernel
theorem block002_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block002 := by
  rw [block002_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0160_nonneg g hg hA hB) (atom0161_nonneg g hg hA hB)) (add_nonneg (atom0162_nonneg g hg hA hB) (add_nonneg (atom0163_nonneg g hg hA hB) (atom0164_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0165_nonneg g hg hA hB) (atom0166_nonneg g hg hA hB)) (add_nonneg (atom0167_nonneg g hg hA hB) (add_nonneg (atom0168_nonneg g hg hA hB) (atom0169_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0170_nonneg g hg hA hB) (atom0171_nonneg g hg hA hB)) (add_nonneg (atom0172_nonneg g hg hA hB) (add_nonneg (atom0173_nonneg g hg hA hB) (atom0174_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0175_nonneg g hg hA hB) (atom0176_nonneg g hg hA hB)) (add_nonneg (atom0177_nonneg g hg hA hB) (add_nonneg (atom0178_nonneg g hg hA hB) (atom0179_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0180_nonneg g hg hA hB) (atom0181_nonneg g hg hA hB)) (add_nonneg (atom0182_nonneg g hg hA hB) (add_nonneg (atom0183_nonneg g hg hA hB) (atom0184_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0185_nonneg g hg hA hB) (atom0186_nonneg g hg hA hB)) (add_nonneg (atom0187_nonneg g hg hA hB) (add_nonneg (atom0188_nonneg g hg hA hB) (atom0189_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0190_nonneg g hg hA hB) (atom0191_nonneg g hg hA hB)) (add_nonneg (atom0192_nonneg g hg hA hB) (add_nonneg (atom0193_nonneg g hg hA hB) (atom0194_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0195_nonneg g hg hA hB) (atom0196_nonneg g hg hA hB)) (add_nonneg (atom0197_nonneg g hg hA hB) (add_nonneg (atom0198_nonneg g hg hA hB) (atom0199_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0200_nonneg g hg hA hB) (atom0201_nonneg g hg hA hB)) (add_nonneg (atom0202_nonneg g hg hA hB) (add_nonneg (atom0203_nonneg g hg hA hB) (atom0204_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0205_nonneg g hg hA hB) (atom0206_nonneg g hg hA hB)) (add_nonneg (atom0207_nonneg g hg hA hB) (add_nonneg (atom0208_nonneg g hg hA hB) (atom0209_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0210_nonneg g hg hA hB) (atom0211_nonneg g hg hA hB)) (add_nonneg (atom0212_nonneg g hg hA hB) (add_nonneg (atom0213_nonneg g hg hA hB) (atom0214_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0215_nonneg g hg hA hB) (atom0216_nonneg g hg hA hB)) (add_nonneg (atom0217_nonneg g hg hA hB) (add_nonneg (atom0218_nonneg g hg hA hB) (atom0219_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0220_nonneg g hg hA hB) (atom0221_nonneg g hg hA hB)) (add_nonneg (atom0222_nonneg g hg hA hB) (add_nonneg (atom0223_nonneg g hg hA hB) (atom0224_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0225_nonneg g hg hA hB) (atom0226_nonneg g hg hA hB)) (add_nonneg (atom0227_nonneg g hg hA hB) (add_nonneg (atom0228_nonneg g hg hA hB) (atom0229_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0230_nonneg g hg hA hB) (atom0231_nonneg g hg hA hB)) (add_nonneg (atom0232_nonneg g hg hA hB) (add_nonneg (atom0233_nonneg g hg hA hB) (atom0234_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0235_nonneg g hg hA hB) (atom0236_nonneg g hg hA hB)) (add_nonneg (atom0237_nonneg g hg hA hB) (add_nonneg (atom0238_nonneg g hg hA hB) (atom0239_nonneg g hg hA hB))))))))

end APPT.Finite12
