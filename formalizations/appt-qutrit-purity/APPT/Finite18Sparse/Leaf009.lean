import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0655 : SparsePolynomial.Poly := [([3,14,14], 1)]
theorem eval_atom0655 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0655 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0655_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8141283000 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656 : SparsePolynomial.Poly := [([3,14,15], 1)]
theorem eval_atom0656 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0656 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0656_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12793243320 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657 : SparsePolynomial.Poly := [([3,14,16], 1)]
theorem eval_atom0657 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0657 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0657_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8558934480 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658 : SparsePolynomial.Poly := [([3,14,17], 1)]
theorem eval_atom0658 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0658 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0658_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11377463760 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659 : SparsePolynomial.Poly := [([3,15,15], 1)]
theorem eval_atom0659 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0659 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0659_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4082641920 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660 : SparsePolynomial.Poly := [([3,15,16], 1)]
theorem eval_atom0660 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0660 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0660_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5228697600 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661 : SparsePolynomial.Poly := [([3,15,17], 1)]
theorem eval_atom0661 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0661 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0661_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8587353600 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662 : SparsePolynomial.Poly := [([3,16,16], 1)]
theorem eval_atom0662 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0662 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0662_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (258048000 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663 : SparsePolynomial.Poly := [([3,16,17], 1)]
theorem eval_atom0663 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0663 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0663_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4255534080 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664 : SparsePolynomial.Poly := [([3,17,17], 1)]
theorem eval_atom0664 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0664 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0664_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3789918720 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0665 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0665 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0665_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (839677440 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom0666 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0666 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0666_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1603536000 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0667 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0667 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0667_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (615212160 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom0668 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0668 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0668_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103864320 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0669 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0669 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0669_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25159680 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670 : SparsePolynomial.Poly := [([4,4,12], 1)]
theorem eval_atom0670 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0670 = ((g 4) * (g 4) * (g 12)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0670_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1531037760 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671 : SparsePolynomial.Poly := [([4,4,14], 1)]
theorem eval_atom0671 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0671 = ((g 4) * (g 4) * (g 14)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0671_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (460951440 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0672 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0672 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0672_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1465409280 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0673 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0673 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0673_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1111580160 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom0674 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0674 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0674_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103864320 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom0675 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0675 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0675_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207728640 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676 : SparsePolynomial.Poly := [([4,5,12], 1)]
theorem eval_atom0676 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0676 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0676_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2424376752 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677 : SparsePolynomial.Poly := [([4,5,14], 1)]
theorem eval_atom0677 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0677 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0677_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1101237360 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678 : SparsePolynomial.Poly := [([4,5,15], 1)]
theorem eval_atom0678 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0678 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0678_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1180247040 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679 : SparsePolynomial.Poly := [([4,5,16], 1)]
theorem eval_atom0679 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0679 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0679_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2293143552 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680 : SparsePolynomial.Poly := [([4,5,17], 1)]
theorem eval_atom0680 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0680 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0680_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3586383360 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0681 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0681 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0681_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (423540480 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom0682 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0682 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0682_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (107089920 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom0683 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0683 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0683_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264499200 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom0684 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0684 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0684_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (421908480 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685 : SparsePolynomial.Poly := [([4,6,12], 1)]
theorem eval_atom0685 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0685 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0685_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2576627520 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686 : SparsePolynomial.Poly := [([4,6,13], 1)]
theorem eval_atom0686 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0686 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0686_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1293281520 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687 : SparsePolynomial.Poly := [([4,6,14], 1)]
theorem eval_atom0687 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0687 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0687_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2694257760 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688 : SparsePolynomial.Poly := [([4,6,15], 1)]
theorem eval_atom0688 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0688 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0688_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3482496240 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0689 : SparsePolynomial.Poly := [([4,6,16], 1)]
theorem eval_atom0689 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0689 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0689_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5041760400 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690 : SparsePolynomial.Poly := [([4,6,17], 1)]
theorem eval_atom0690 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0690 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0690_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6677153280 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0691 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0691 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0691_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (353829120 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0692 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0692 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0692_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (403703040 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom0693 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0693 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0693_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (460473600 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom0694 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0694 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0694_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (621108480 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom0695 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0695 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0695_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (781743360 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696 : SparsePolynomial.Poly := [([4,7,12], 1)]
theorem eval_atom0696 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0696 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0696_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3019296000 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697 : SparsePolynomial.Poly := [([4,7,13], 1)]
theorem eval_atom0697 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0697 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0697_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2332497120 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698 : SparsePolynomial.Poly := [([4,7,14], 1)]
theorem eval_atom0698 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0698 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0698_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4135339680 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699 : SparsePolynomial.Poly := [([4,7,15], 1)]
theorem eval_atom0699 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0699 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0699_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5254997280 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700 : SparsePolynomial.Poly := [([4,7,16], 1)]
theorem eval_atom0700 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0700 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0700_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7178238240 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701 : SparsePolynomial.Poly := [([4,7,17], 1)]
theorem eval_atom0701 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0701 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0701_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9115705440 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0702 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0702 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0702_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (827243520 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703 : SparsePolynomial.Poly := [([4,8,9], 1)]
theorem eval_atom0703 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0703 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0703_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1400517120 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704 : SparsePolynomial.Poly := [([4,8,10], 1)]
theorem eval_atom0704 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0704 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0704_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1514058240 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705 : SparsePolynomial.Poly := [([4,8,11], 1)]
theorem eval_atom0705 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0705 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0705_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1627599360 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706 : SparsePolynomial.Poly := [([4,8,12], 1)]
theorem eval_atom0706 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0706 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0706_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3755136000 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707 : SparsePolynomial.Poly := [([4,8,13], 1)]
theorem eval_atom0707 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0707 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0707_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3303554880 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708 : SparsePolynomial.Poly := [([4,8,14], 1)]
theorem eval_atom0708 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0708 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0708_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5488183200 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709 : SparsePolynomial.Poly := [([4,8,15], 1)]
theorem eval_atom0709 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0709 = ((g 4) * (g 8) * (g 15)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0709_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6428383680 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710 : SparsePolynomial.Poly := [([4,8,16], 1)]
theorem eval_atom0710 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0710 = ((g 4) * (g 8) * (g 16)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0710_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8473755840 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711 : SparsePolynomial.Poly := [([4,8,17], 1)]
theorem eval_atom0711 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0711 = ((g 4) * (g 8) * (g 17)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0711_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10519128000 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom0712 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0712 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0712_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1454507520 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713 : SparsePolynomial.Poly := [([4,9,10], 1)]
theorem eval_atom0713 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0713 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0713_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2574428160 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714 : SparsePolynomial.Poly := [([4,9,11], 1)]
theorem eval_atom0714 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0714 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0714_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2590556160 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715 : SparsePolynomial.Poly := [([4,9,12], 1)]
theorem eval_atom0715 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0715 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0715_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4644494400 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716 : SparsePolynomial.Poly := [([4,9,13], 1)]
theorem eval_atom0716 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0716 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0716_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4143129600 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717 : SparsePolynomial.Poly := [([4,9,14], 1)]
theorem eval_atom0717 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0717 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0717_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6663591840 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718 : SparsePolynomial.Poly := [([4,9,15], 1)]
theorem eval_atom0718 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0718 = ((g 4) * (g 9) * (g 15)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0718_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7216020480 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719 : SparsePolynomial.Poly := [([4,9,16], 1)]
theorem eval_atom0719 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0719 = ((g 4) * (g 9) * (g 16)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0719_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9259238400 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720 : SparsePolynomial.Poly := [([4,9,17], 1)]
theorem eval_atom0720 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0720 = ((g 4) * (g 9) * (g 17)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0720_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11302456320 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721 : SparsePolynomial.Poly := [([4,10,10], 1)]
theorem eval_atom0721 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0721 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0721_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2105018880 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722 : SparsePolynomial.Poly := [([4,10,11], 1)]
theorem eval_atom0722 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0722 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0722_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3744445440 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723 : SparsePolynomial.Poly := [([4,10,12], 1)]
theorem eval_atom0723 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0723 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0723_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5639632320 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724 : SparsePolynomial.Poly := [([4,10,13], 1)]
theorem eval_atom0724 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0724 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0724_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4968497280 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725 : SparsePolynomial.Poly := [([4,10,14], 1)]
theorem eval_atom0725 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0725 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0725_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7889319840 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726 : SparsePolynomial.Poly := [([4,10,15], 1)]
theorem eval_atom0726 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0726 = ((g 4) * (g 10) * (g 15)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0726_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7679809920 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727 : SparsePolynomial.Poly := [([4,10,16], 1)]
theorem eval_atom0727 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0727 = ((g 4) * (g 10) * (g 16)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0727_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9531219840 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728 : SparsePolynomial.Poly := [([4,10,17], 1)]
theorem eval_atom0728 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0728 = ((g 4) * (g 10) * (g 17)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0728_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11673385920 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729 : SparsePolynomial.Poly := [([4,11,11], 1)]
theorem eval_atom0729 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0729 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0729_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2958144000 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730 : SparsePolynomial.Poly := [([4,11,12], 1)]
theorem eval_atom0730 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0730 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0730_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6511653120 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731 : SparsePolynomial.Poly := [([4,11,13], 1)]
theorem eval_atom0731 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0731 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0731_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5589568320 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732 : SparsePolynomial.Poly := [([4,11,14], 1)]
theorem eval_atom0732 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0732 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0732_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8928903840 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733 : SparsePolynomial.Poly := [([4,11,15], 1)]
theorem eval_atom0733 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0733 = ((g 4) * (g 11) * (g 15)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0733_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8835408960 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734 : SparsePolynomial.Poly := [([4,11,16], 1)]
theorem eval_atom0734 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0734 = ((g 4) * (g 11) * (g 16)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0734_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9405332160 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block009 : SparsePolynomial.Poly := [([3,14,14], 8141283000), ([3,14,15], 12793243320), ([3,14,16], 8558934480), ([3,14,17], 11377463760), ([3,15,15], 4082641920), ([3,15,16], 5228697600), ([3,15,17], 8587353600), ([3,16,16], 258048000), ([3,16,17], 4255534080), ([3,17,17], 3789918720), ([4,4,4], 839677440), ([4,4,5], 1603536000), ([4,4,6], 615212160), ([4,4,7], 103864320), ([4,4,8], 25159680), ([4,4,12], 1531037760), ([4,4,14], 460951440), ([4,5,5], 1465409280), ([4,5,6], 1111580160), ([4,5,10], 103864320), ([4,5,11], 207728640), ([4,5,12], 2424376752), ([4,5,14], 1101237360), ([4,5,15], 1180247040), ([4,5,16], 2293143552), ([4,5,17], 3586383360), ([4,6,6], 423540480), ([4,6,9], 107089920), ([4,6,10], 264499200), ([4,6,11], 421908480), ([4,6,12], 2576627520), ([4,6,13], 1293281520), ([4,6,14], 2694257760), ([4,6,15], 3482496240), ([4,6,16], 5041760400), ([4,6,17], 6677153280), ([4,7,7], 353829120), ([4,7,8], 403703040), ([4,7,9], 460473600), ([4,7,10], 621108480), ([4,7,11], 781743360), ([4,7,12], 3019296000), ([4,7,13], 2332497120), ([4,7,14], 4135339680), ([4,7,15], 5254997280), ([4,7,16], 7178238240), ([4,7,17], 9115705440), ([4,8,8], 827243520), ([4,8,9], 1400517120), ([4,8,10], 1514058240), ([4,8,11], 1627599360), ([4,8,12], 3755136000), ([4,8,13], 3303554880), ([4,8,14], 5488183200), ([4,8,15], 6428383680), ([4,8,16], 8473755840), ([4,8,17], 10519128000), ([4,9,9], 1454507520), ([4,9,10], 2574428160), ([4,9,11], 2590556160), ([4,9,12], 4644494400), ([4,9,13], 4143129600), ([4,9,14], 6663591840), ([4,9,15], 7216020480), ([4,9,16], 9259238400), ([4,9,17], 11302456320), ([4,10,10], 2105018880), ([4,10,11], 3744445440), ([4,10,12], 5639632320), ([4,10,13], 4968497280), ([4,10,14], 7889319840), ([4,10,15], 7679809920), ([4,10,16], 9531219840), ([4,10,17], 11673385920), ([4,11,11], 2958144000), ([4,11,12], 6511653120), ([4,11,13], 5589568320), ([4,11,14], 8928903840), ([4,11,15], 8835408960), ([4,11,16], 9405332160)]
theorem block009_data : block009 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8141283000 : Int) atom0655) (SparsePolynomial.scale (12793243320 : Int) atom0656)) (SparsePolynomial.merge (SparsePolynomial.scale (8558934480 : Int) atom0657) (SparsePolynomial.merge (SparsePolynomial.scale (11377463760 : Int) atom0658) (SparsePolynomial.scale (4082641920 : Int) atom0659)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5228697600 : Int) atom0660) (SparsePolynomial.scale (8587353600 : Int) atom0661)) (SparsePolynomial.merge (SparsePolynomial.scale (258048000 : Int) atom0662) (SparsePolynomial.merge (SparsePolynomial.scale (4255534080 : Int) atom0663) (SparsePolynomial.scale (3789918720 : Int) atom0664))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (839677440 : Int) atom0665) (SparsePolynomial.scale (1603536000 : Int) atom0666)) (SparsePolynomial.merge (SparsePolynomial.scale (615212160 : Int) atom0667) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0668) (SparsePolynomial.scale (25159680 : Int) atom0669)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1531037760 : Int) atom0670) (SparsePolynomial.scale (460951440 : Int) atom0671)) (SparsePolynomial.merge (SparsePolynomial.scale (1465409280 : Int) atom0672) (SparsePolynomial.merge (SparsePolynomial.scale (1111580160 : Int) atom0673) (SparsePolynomial.scale (103864320 : Int) atom0674)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (207728640 : Int) atom0675) (SparsePolynomial.scale (2424376752 : Int) atom0676)) (SparsePolynomial.merge (SparsePolynomial.scale (1101237360 : Int) atom0677) (SparsePolynomial.merge (SparsePolynomial.scale (1180247040 : Int) atom0678) (SparsePolynomial.scale (2293143552 : Int) atom0679)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3586383360 : Int) atom0680) (SparsePolynomial.scale (423540480 : Int) atom0681)) (SparsePolynomial.merge (SparsePolynomial.scale (107089920 : Int) atom0682) (SparsePolynomial.merge (SparsePolynomial.scale (264499200 : Int) atom0683) (SparsePolynomial.scale (421908480 : Int) atom0684))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2576627520 : Int) atom0685) (SparsePolynomial.scale (1293281520 : Int) atom0686)) (SparsePolynomial.merge (SparsePolynomial.scale (2694257760 : Int) atom0687) (SparsePolynomial.merge (SparsePolynomial.scale (3482496240 : Int) atom0688) (SparsePolynomial.scale (5041760400 : Int) atom0689)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6677153280 : Int) atom0690) (SparsePolynomial.scale (353829120 : Int) atom0691)) (SparsePolynomial.merge (SparsePolynomial.scale (403703040 : Int) atom0692) (SparsePolynomial.merge (SparsePolynomial.scale (460473600 : Int) atom0693) (SparsePolynomial.scale (621108480 : Int) atom0694))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (781743360 : Int) atom0695) (SparsePolynomial.scale (3019296000 : Int) atom0696)) (SparsePolynomial.merge (SparsePolynomial.scale (2332497120 : Int) atom0697) (SparsePolynomial.merge (SparsePolynomial.scale (4135339680 : Int) atom0698) (SparsePolynomial.scale (5254997280 : Int) atom0699)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7178238240 : Int) atom0700) (SparsePolynomial.scale (9115705440 : Int) atom0701)) (SparsePolynomial.merge (SparsePolynomial.scale (827243520 : Int) atom0702) (SparsePolynomial.merge (SparsePolynomial.scale (1400517120 : Int) atom0703) (SparsePolynomial.scale (1514058240 : Int) atom0704))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1627599360 : Int) atom0705) (SparsePolynomial.scale (3755136000 : Int) atom0706)) (SparsePolynomial.merge (SparsePolynomial.scale (3303554880 : Int) atom0707) (SparsePolynomial.merge (SparsePolynomial.scale (5488183200 : Int) atom0708) (SparsePolynomial.scale (6428383680 : Int) atom0709)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8473755840 : Int) atom0710) (SparsePolynomial.scale (10519128000 : Int) atom0711)) (SparsePolynomial.merge (SparsePolynomial.scale (1454507520 : Int) atom0712) (SparsePolynomial.merge (SparsePolynomial.scale (2574428160 : Int) atom0713) (SparsePolynomial.scale (2590556160 : Int) atom0714)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4644494400 : Int) atom0715) (SparsePolynomial.scale (4143129600 : Int) atom0716)) (SparsePolynomial.merge (SparsePolynomial.scale (6663591840 : Int) atom0717) (SparsePolynomial.merge (SparsePolynomial.scale (7216020480 : Int) atom0718) (SparsePolynomial.scale (9259238400 : Int) atom0719)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11302456320 : Int) atom0720) (SparsePolynomial.scale (2105018880 : Int) atom0721)) (SparsePolynomial.merge (SparsePolynomial.scale (3744445440 : Int) atom0722) (SparsePolynomial.merge (SparsePolynomial.scale (5639632320 : Int) atom0723) (SparsePolynomial.scale (4968497280 : Int) atom0724))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7889319840 : Int) atom0725) (SparsePolynomial.scale (7679809920 : Int) atom0726)) (SparsePolynomial.merge (SparsePolynomial.scale (9531219840 : Int) atom0727) (SparsePolynomial.merge (SparsePolynomial.scale (11673385920 : Int) atom0728) (SparsePolynomial.scale (2958144000 : Int) atom0729)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6511653120 : Int) atom0730) (SparsePolynomial.scale (5589568320 : Int) atom0731)) (SparsePolynomial.merge (SparsePolynomial.scale (8928903840 : Int) atom0732) (SparsePolynomial.merge (SparsePolynomial.scale (8835408960 : Int) atom0733) (SparsePolynomial.scale (9405332160 : Int) atom0734)))))))) := by decide +kernel
theorem block009_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block009 := by
  rw [block009_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0655_nonneg g hg hA hB) (atom0656_nonneg g hg hA hB)) (add_nonneg (atom0657_nonneg g hg hA hB) (add_nonneg (atom0658_nonneg g hg hA hB) (atom0659_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0660_nonneg g hg hA hB) (atom0661_nonneg g hg hA hB)) (add_nonneg (atom0662_nonneg g hg hA hB) (add_nonneg (atom0663_nonneg g hg hA hB) (atom0664_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0665_nonneg g hg hA hB) (atom0666_nonneg g hg hA hB)) (add_nonneg (atom0667_nonneg g hg hA hB) (add_nonneg (atom0668_nonneg g hg hA hB) (atom0669_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0670_nonneg g hg hA hB) (atom0671_nonneg g hg hA hB)) (add_nonneg (atom0672_nonneg g hg hA hB) (add_nonneg (atom0673_nonneg g hg hA hB) (atom0674_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0675_nonneg g hg hA hB) (atom0676_nonneg g hg hA hB)) (add_nonneg (atom0677_nonneg g hg hA hB) (add_nonneg (atom0678_nonneg g hg hA hB) (atom0679_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0680_nonneg g hg hA hB) (atom0681_nonneg g hg hA hB)) (add_nonneg (atom0682_nonneg g hg hA hB) (add_nonneg (atom0683_nonneg g hg hA hB) (atom0684_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0685_nonneg g hg hA hB) (atom0686_nonneg g hg hA hB)) (add_nonneg (atom0687_nonneg g hg hA hB) (add_nonneg (atom0688_nonneg g hg hA hB) (atom0689_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0690_nonneg g hg hA hB) (atom0691_nonneg g hg hA hB)) (add_nonneg (atom0692_nonneg g hg hA hB) (add_nonneg (atom0693_nonneg g hg hA hB) (atom0694_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0695_nonneg g hg hA hB) (atom0696_nonneg g hg hA hB)) (add_nonneg (atom0697_nonneg g hg hA hB) (add_nonneg (atom0698_nonneg g hg hA hB) (atom0699_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0700_nonneg g hg hA hB) (atom0701_nonneg g hg hA hB)) (add_nonneg (atom0702_nonneg g hg hA hB) (add_nonneg (atom0703_nonneg g hg hA hB) (atom0704_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0705_nonneg g hg hA hB) (atom0706_nonneg g hg hA hB)) (add_nonneg (atom0707_nonneg g hg hA hB) (add_nonneg (atom0708_nonneg g hg hA hB) (atom0709_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0710_nonneg g hg hA hB) (atom0711_nonneg g hg hA hB)) (add_nonneg (atom0712_nonneg g hg hA hB) (add_nonneg (atom0713_nonneg g hg hA hB) (atom0714_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0715_nonneg g hg hA hB) (atom0716_nonneg g hg hA hB)) (add_nonneg (atom0717_nonneg g hg hA hB) (add_nonneg (atom0718_nonneg g hg hA hB) (atom0719_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0720_nonneg g hg hA hB) (atom0721_nonneg g hg hA hB)) (add_nonneg (atom0722_nonneg g hg hA hB) (add_nonneg (atom0723_nonneg g hg hA hB) (atom0724_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0725_nonneg g hg hA hB) (atom0726_nonneg g hg hA hB)) (add_nonneg (atom0727_nonneg g hg hA hB) (add_nonneg (atom0728_nonneg g hg hA hB) (atom0729_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0730_nonneg g hg hA hB) (atom0731_nonneg g hg hA hB)) (add_nonneg (atom0732_nonneg g hg hA hB) (add_nonneg (atom0733_nonneg g hg hA hB) (atom0734_nonneg g hg hA hB))))))))

end APPT.Finite18
