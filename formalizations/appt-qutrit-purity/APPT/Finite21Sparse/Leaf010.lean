import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0656 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0656 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0656 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0656_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37423734021504 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0657 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0657 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0657_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34748060719104 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0658 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0658 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0658_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34509342530304 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0659 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0659 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0659_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34217714824704 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660 : SparsePolynomial.Poly := [([2,7,12], 1)]
theorem eval_atom0660 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0660 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0660_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31960616904704 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661 : SparsePolynomial.Poly := [([2,7,13], 1)]
theorem eval_atom0661 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0661 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0661_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31446597832704 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662 : SparsePolynomial.Poly := [([2,7,14], 1)]
theorem eval_atom0662 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0662 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0662_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31809990703104 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663 : SparsePolynomial.Poly := [([2,7,15], 1)]
theorem eval_atom0663 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0663 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0663_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41404370635008 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664 : SparsePolynomial.Poly := [([2,7,16], 1)]
theorem eval_atom0664 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0664 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0664_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31000486141440 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665 : SparsePolynomial.Poly := [([2,7,17], 1)]
theorem eval_atom0665 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0665 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0665_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41272519396608 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666 : SparsePolynomial.Poly := [([2,7,18], 1)]
theorem eval_atom0666 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0666 = ((g 2) * (g 7) * (g 18)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0666_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36889019085312 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667 : SparsePolynomial.Poly := [([2,7,19], 1)]
theorem eval_atom0667 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0667 = ((g 2) * (g 7) * (g 19)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0667_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40093076482560 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668 : SparsePolynomial.Poly := [([2,7,20], 1)]
theorem eval_atom0668 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0668 = ((g 2) * (g 7) * (g 20)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0668_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47967118852608 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0669 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0669 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0669_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22303076342400 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0670 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0670 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0670_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41607678268800 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0671 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0671 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0671_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40696296681600 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0672 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0672 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0672_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39732005577600 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0673 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0673 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0673_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36634078409600 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0674 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0674 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0674_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35706410006400 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0675 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0675 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0675_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35656153545600 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676 : SparsePolynomial.Poly := [([2,8,15], 1)]
theorem eval_atom0676 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0676 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0676_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44345527833600 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677 : SparsePolynomial.Poly := [([2,8,16], 1)]
theorem eval_atom0677 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0677 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0677_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34468180210800 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678 : SparsePolynomial.Poly := [([2,8,17], 1)]
theorem eval_atom0678 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0678 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0678_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45222671692800 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679 : SparsePolynomial.Poly := [([2,8,18], 1)]
theorem eval_atom0679 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0679 = ((g 2) * (g 8) * (g 18)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0679_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40427074270800 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680 : SparsePolynomial.Poly := [([2,8,19], 1)]
theorem eval_atom0680 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0680 = ((g 2) * (g 8) * (g 19)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0680_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43815922189200 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681 : SparsePolynomial.Poly := [([2,8,20], 1)]
theorem eval_atom0681 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0681 = ((g 2) * (g 8) * (g 20)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0681_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51874755080400 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0682 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0682 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0682_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24598926777600 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0683 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0683 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0683_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46170868262400 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0684 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0684 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0684_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44365747910400 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0685 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0685 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0685_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41113185478400 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0686 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0686 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0686_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39603701894400 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0687 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0687 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0687_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38971630252800 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688 : SparsePolynomial.Poly := [([2,9,15], 1)]
theorem eval_atom0688 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0688 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0688_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47136694348800 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0689 : SparsePolynomial.Poly := [([2,9,16], 1)]
theorem eval_atom0689 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0689 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0689_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37088825104800 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690 : SparsePolynomial.Poly := [([2,9,17], 1)]
theorem eval_atom0690 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0690 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0690_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49022833305600 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691 : SparsePolynomial.Poly := [([2,9,18], 1)]
theorem eval_atom0691 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0691 = ((g 2) * (g 9) * (g 18)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0691_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42821685900000 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692 : SparsePolynomial.Poly := [([2,9,19], 1)]
theorem eval_atom0692 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0692 = ((g 2) * (g 9) * (g 19)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0692_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46253783368800 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693 : SparsePolynomial.Poly := [([2,9,20], 1)]
theorem eval_atom0693 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0693 = ((g 2) * (g 9) * (g 20)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0693_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54355865810400 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0694 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0694 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0694_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26866266336000 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0695 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0695 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0695_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50413919673600 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0696 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0696 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0696_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45984196294400 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697 : SparsePolynomial.Poly := [([2,10,13], 1)]
theorem eval_atom0697 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0697 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0697_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43724731680000 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698 : SparsePolynomial.Poly := [([2,10,14], 1)]
theorem eval_atom0698 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0698 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0698_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42342679008000 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699 : SparsePolynomial.Poly := [([2,10,15], 1)]
theorem eval_atom0699 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0699 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0699_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49927860864000 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700 : SparsePolynomial.Poly := [([2,10,16], 1)]
theorem eval_atom0700 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0700 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0700_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39228832188000 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701 : SparsePolynomial.Poly := [([2,10,17], 1)]
theorem eval_atom0701 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0701 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0701_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52822994918400 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702 : SparsePolynomial.Poly := [([2,10,18], 1)]
theorem eval_atom0702 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0702 = ((g 2) * (g 10) * (g 18)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0702_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43999571700000 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703 : SparsePolynomial.Poly := [([2,10,19], 1)]
theorem eval_atom0703 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0703 = ((g 2) * (g 10) * (g 19)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0703_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47040248656800 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704 : SparsePolynomial.Poly := [([2,10,20], 1)]
theorem eval_atom0704 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0704 = ((g 2) * (g 10) * (g 20)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0704_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54750910586400 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0705 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0705 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0705_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28841978188800 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706 : SparsePolynomial.Poly := [([2,11,12], 1)]
theorem eval_atom0706 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0706 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0706_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50886380518400 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707 : SparsePolynomial.Poly := [([2,11,13], 1)]
theorem eval_atom0707 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0707 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0707_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47708769024000 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708 : SparsePolynomial.Poly := [([2,11,14], 1)]
theorem eval_atom0708 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0708 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0708_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45408569472000 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709 : SparsePolynomial.Poly := [([2,11,15], 1)]
theorem eval_atom0709 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0709 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0709_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52095180211200 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710 : SparsePolynomial.Poly := [([2,11,16], 1)]
theorem eval_atom0710 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0710 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0710_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40662744998400 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711 : SparsePolynomial.Poly := [([2,11,17], 1)]
theorem eval_atom0711 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0711 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0711_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55999309363200 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712 : SparsePolynomial.Poly := [([2,11,18], 1)]
theorem eval_atom0712 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0712 = ((g 2) * (g 11) * (g 18)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0712_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44005822963200 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713 : SparsePolynomial.Poly := [([2,11,19], 1)]
theorem eval_atom0713 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0713 = ((g 2) * (g 11) * (g 19)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0713_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46400774515200 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714 : SparsePolynomial.Poly := [([2,11,20], 1)]
theorem eval_atom0714 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0714 = ((g 2) * (g 11) * (g 20)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0714_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53465711040000 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715 : SparsePolynomial.Poly := [([2,12,12], 1)]
theorem eval_atom0715 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0715 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0715_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27765907097600 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716 : SparsePolynomial.Poly := [([2,12,13], 1)]
theorem eval_atom0716 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0716 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0716_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50840710054400 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717 : SparsePolynomial.Poly := [([2,12,14], 1)]
theorem eval_atom0717 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0717 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0717_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47454197772800 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718 : SparsePolynomial.Poly := [([2,12,15], 1)]
theorem eval_atom0718 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0718 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0718_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50163393280000 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719 : SparsePolynomial.Poly := [([2,12,16], 1)]
theorem eval_atom0719 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0719 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0719_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40943623616000 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720 : SparsePolynomial.Poly := [([2,12,17], 1)]
theorem eval_atom0720 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0720 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0720_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55076517529600 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721 : SparsePolynomial.Poly := [([2,12,18], 1)]
theorem eval_atom0721 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0721 = ((g 2) * (g 12) * (g 18)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0721_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43587528678400 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722 : SparsePolynomial.Poly := [([2,12,19], 1)]
theorem eval_atom0722 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0722 = ((g 2) * (g 12) * (g 19)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0722_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44782300864000 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723 : SparsePolynomial.Poly := [([2,12,20], 1)]
theorem eval_atom0723 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0723 = ((g 2) * (g 12) * (g 20)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0723_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51304759027200 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724 : SparsePolynomial.Poly := [([2,13,13], 1)]
theorem eval_atom0724 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0724 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0724_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28504801843200 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725 : SparsePolynomial.Poly := [([2,13,14], 1)]
theorem eval_atom0725 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0725 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0725_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51198079104000 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726 : SparsePolynomial.Poly := [([2,13,15], 1)]
theorem eval_atom0726 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0726 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0726_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52516793448000 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727 : SparsePolynomial.Poly := [([2,13,16], 1)]
theorem eval_atom0727 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0727 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0727_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41770540036800 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728 : SparsePolynomial.Poly := [([2,13,17], 1)]
theorem eval_atom0728 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0728 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0728_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57639883392000 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729 : SparsePolynomial.Poly := [([2,13,18], 1)]
theorem eval_atom0729 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0729 = ((g 2) * (g 13) * (g 18)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0729_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46655392089600 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730 : SparsePolynomial.Poly := [([2,13,19], 1)]
theorem eval_atom0730 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0730 = ((g 2) * (g 13) * (g 19)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0730_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40485755707200 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731 : SparsePolynomial.Poly := [([2,13,20], 1)]
theorem eval_atom0731 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0731 = ((g 2) * (g 13) * (g 20)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0731_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52168139251200 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732 : SparsePolynomial.Poly := [([2,14,14], 1)]
theorem eval_atom0732 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0732 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0732_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30391628198400 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733 : SparsePolynomial.Poly := [([2,14,15], 1)]
theorem eval_atom0733 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0733 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0733_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (55197057484800 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734 : SparsePolynomial.Poly := [([2,14,16], 1)]
theorem eval_atom0734 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0734 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0734_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42478307020800 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0735 : SparsePolynomial.Poly := [([2,14,17], 1)]
theorem eval_atom0735 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0735 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0735_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61958073139200 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block010 : SparsePolynomial.Poly := [([2,7,8], 37423734021504), ([2,7,9], 34748060719104), ([2,7,10], 34509342530304), ([2,7,11], 34217714824704), ([2,7,12], 31960616904704), ([2,7,13], 31446597832704), ([2,7,14], 31809990703104), ([2,7,15], 41404370635008), ([2,7,16], 31000486141440), ([2,7,17], 41272519396608), ([2,7,18], 36889019085312), ([2,7,19], 40093076482560), ([2,7,20], 47967118852608), ([2,8,8], 22303076342400), ([2,8,9], 41607678268800), ([2,8,10], 40696296681600), ([2,8,11], 39732005577600), ([2,8,12], 36634078409600), ([2,8,13], 35706410006400), ([2,8,14], 35656153545600), ([2,8,15], 44345527833600), ([2,8,16], 34468180210800), ([2,8,17], 45222671692800), ([2,8,18], 40427074270800), ([2,8,19], 43815922189200), ([2,8,20], 51874755080400), ([2,9,9], 24598926777600), ([2,9,10], 46170868262400), ([2,9,11], 44365747910400), ([2,9,12], 41113185478400), ([2,9,13], 39603701894400), ([2,9,14], 38971630252800), ([2,9,15], 47136694348800), ([2,9,16], 37088825104800), ([2,9,17], 49022833305600), ([2,9,18], 42821685900000), ([2,9,19], 46253783368800), ([2,9,20], 54355865810400), ([2,10,10], 26866266336000), ([2,10,11], 50413919673600), ([2,10,12], 45984196294400), ([2,10,13], 43724731680000), ([2,10,14], 42342679008000), ([2,10,15], 49927860864000), ([2,10,16], 39228832188000), ([2,10,17], 52822994918400), ([2,10,18], 43999571700000), ([2,10,19], 47040248656800), ([2,10,20], 54750910586400), ([2,11,11], 28841978188800), ([2,11,12], 50886380518400), ([2,11,13], 47708769024000), ([2,11,14], 45408569472000), ([2,11,15], 52095180211200), ([2,11,16], 40662744998400), ([2,11,17], 55999309363200), ([2,11,18], 44005822963200), ([2,11,19], 46400774515200), ([2,11,20], 53465711040000), ([2,12,12], 27765907097600), ([2,12,13], 50840710054400), ([2,12,14], 47454197772800), ([2,12,15], 50163393280000), ([2,12,16], 40943623616000), ([2,12,17], 55076517529600), ([2,12,18], 43587528678400), ([2,12,19], 44782300864000), ([2,12,20], 51304759027200), ([2,13,13], 28504801843200), ([2,13,14], 51198079104000), ([2,13,15], 52516793448000), ([2,13,16], 41770540036800), ([2,13,17], 57639883392000), ([2,13,18], 46655392089600), ([2,13,19], 40485755707200), ([2,13,20], 52168139251200), ([2,14,14], 30391628198400), ([2,14,15], 55197057484800), ([2,14,16], 42478307020800), ([2,14,17], 61958073139200)]
theorem block010_data : block010 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37423734021504 : Int) atom0656) (SparsePolynomial.scale (34748060719104 : Int) atom0657)) (SparsePolynomial.merge (SparsePolynomial.scale (34509342530304 : Int) atom0658) (SparsePolynomial.merge (SparsePolynomial.scale (34217714824704 : Int) atom0659) (SparsePolynomial.scale (31960616904704 : Int) atom0660)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31446597832704 : Int) atom0661) (SparsePolynomial.scale (31809990703104 : Int) atom0662)) (SparsePolynomial.merge (SparsePolynomial.scale (41404370635008 : Int) atom0663) (SparsePolynomial.merge (SparsePolynomial.scale (31000486141440 : Int) atom0664) (SparsePolynomial.scale (41272519396608 : Int) atom0665))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36889019085312 : Int) atom0666) (SparsePolynomial.scale (40093076482560 : Int) atom0667)) (SparsePolynomial.merge (SparsePolynomial.scale (47967118852608 : Int) atom0668) (SparsePolynomial.merge (SparsePolynomial.scale (22303076342400 : Int) atom0669) (SparsePolynomial.scale (41607678268800 : Int) atom0670)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (40696296681600 : Int) atom0671) (SparsePolynomial.scale (39732005577600 : Int) atom0672)) (SparsePolynomial.merge (SparsePolynomial.scale (36634078409600 : Int) atom0673) (SparsePolynomial.merge (SparsePolynomial.scale (35706410006400 : Int) atom0674) (SparsePolynomial.scale (35656153545600 : Int) atom0675)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (44345527833600 : Int) atom0676) (SparsePolynomial.scale (34468180210800 : Int) atom0677)) (SparsePolynomial.merge (SparsePolynomial.scale (45222671692800 : Int) atom0678) (SparsePolynomial.merge (SparsePolynomial.scale (40427074270800 : Int) atom0679) (SparsePolynomial.scale (43815922189200 : Int) atom0680)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (51874755080400 : Int) atom0681) (SparsePolynomial.scale (24598926777600 : Int) atom0682)) (SparsePolynomial.merge (SparsePolynomial.scale (46170868262400 : Int) atom0683) (SparsePolynomial.merge (SparsePolynomial.scale (44365747910400 : Int) atom0684) (SparsePolynomial.scale (41113185478400 : Int) atom0685))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39603701894400 : Int) atom0686) (SparsePolynomial.scale (38971630252800 : Int) atom0687)) (SparsePolynomial.merge (SparsePolynomial.scale (47136694348800 : Int) atom0688) (SparsePolynomial.merge (SparsePolynomial.scale (37088825104800 : Int) atom0689) (SparsePolynomial.scale (49022833305600 : Int) atom0690)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (42821685900000 : Int) atom0691) (SparsePolynomial.scale (46253783368800 : Int) atom0692)) (SparsePolynomial.merge (SparsePolynomial.scale (54355865810400 : Int) atom0693) (SparsePolynomial.merge (SparsePolynomial.scale (26866266336000 : Int) atom0694) (SparsePolynomial.scale (50413919673600 : Int) atom0695))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (45984196294400 : Int) atom0696) (SparsePolynomial.scale (43724731680000 : Int) atom0697)) (SparsePolynomial.merge (SparsePolynomial.scale (42342679008000 : Int) atom0698) (SparsePolynomial.merge (SparsePolynomial.scale (49927860864000 : Int) atom0699) (SparsePolynomial.scale (39228832188000 : Int) atom0700)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52822994918400 : Int) atom0701) (SparsePolynomial.scale (43999571700000 : Int) atom0702)) (SparsePolynomial.merge (SparsePolynomial.scale (47040248656800 : Int) atom0703) (SparsePolynomial.merge (SparsePolynomial.scale (54750910586400 : Int) atom0704) (SparsePolynomial.scale (28841978188800 : Int) atom0705))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (50886380518400 : Int) atom0706) (SparsePolynomial.scale (47708769024000 : Int) atom0707)) (SparsePolynomial.merge (SparsePolynomial.scale (45408569472000 : Int) atom0708) (SparsePolynomial.merge (SparsePolynomial.scale (52095180211200 : Int) atom0709) (SparsePolynomial.scale (40662744998400 : Int) atom0710)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55999309363200 : Int) atom0711) (SparsePolynomial.scale (44005822963200 : Int) atom0712)) (SparsePolynomial.merge (SparsePolynomial.scale (46400774515200 : Int) atom0713) (SparsePolynomial.merge (SparsePolynomial.scale (53465711040000 : Int) atom0714) (SparsePolynomial.scale (27765907097600 : Int) atom0715)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (50840710054400 : Int) atom0716) (SparsePolynomial.scale (47454197772800 : Int) atom0717)) (SparsePolynomial.merge (SparsePolynomial.scale (50163393280000 : Int) atom0718) (SparsePolynomial.merge (SparsePolynomial.scale (40943623616000 : Int) atom0719) (SparsePolynomial.scale (55076517529600 : Int) atom0720)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (43587528678400 : Int) atom0721) (SparsePolynomial.scale (44782300864000 : Int) atom0722)) (SparsePolynomial.merge (SparsePolynomial.scale (51304759027200 : Int) atom0723) (SparsePolynomial.merge (SparsePolynomial.scale (28504801843200 : Int) atom0724) (SparsePolynomial.scale (51198079104000 : Int) atom0725))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52516793448000 : Int) atom0726) (SparsePolynomial.scale (41770540036800 : Int) atom0727)) (SparsePolynomial.merge (SparsePolynomial.scale (57639883392000 : Int) atom0728) (SparsePolynomial.merge (SparsePolynomial.scale (46655392089600 : Int) atom0729) (SparsePolynomial.scale (40485755707200 : Int) atom0730)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52168139251200 : Int) atom0731) (SparsePolynomial.scale (30391628198400 : Int) atom0732)) (SparsePolynomial.merge (SparsePolynomial.scale (55197057484800 : Int) atom0733) (SparsePolynomial.merge (SparsePolynomial.scale (42478307020800 : Int) atom0734) (SparsePolynomial.scale (61958073139200 : Int) atom0735)))))))) := by decide +kernel
theorem block010_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block010 := by
  rw [block010_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0656_nonneg g hg hA hB) (atom0657_nonneg g hg hA hB)) (add_nonneg (atom0658_nonneg g hg hA hB) (add_nonneg (atom0659_nonneg g hg hA hB) (atom0660_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0661_nonneg g hg hA hB) (atom0662_nonneg g hg hA hB)) (add_nonneg (atom0663_nonneg g hg hA hB) (add_nonneg (atom0664_nonneg g hg hA hB) (atom0665_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0666_nonneg g hg hA hB) (atom0667_nonneg g hg hA hB)) (add_nonneg (atom0668_nonneg g hg hA hB) (add_nonneg (atom0669_nonneg g hg hA hB) (atom0670_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0671_nonneg g hg hA hB) (atom0672_nonneg g hg hA hB)) (add_nonneg (atom0673_nonneg g hg hA hB) (add_nonneg (atom0674_nonneg g hg hA hB) (atom0675_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0676_nonneg g hg hA hB) (atom0677_nonneg g hg hA hB)) (add_nonneg (atom0678_nonneg g hg hA hB) (add_nonneg (atom0679_nonneg g hg hA hB) (atom0680_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0681_nonneg g hg hA hB) (atom0682_nonneg g hg hA hB)) (add_nonneg (atom0683_nonneg g hg hA hB) (add_nonneg (atom0684_nonneg g hg hA hB) (atom0685_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0686_nonneg g hg hA hB) (atom0687_nonneg g hg hA hB)) (add_nonneg (atom0688_nonneg g hg hA hB) (add_nonneg (atom0689_nonneg g hg hA hB) (atom0690_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0691_nonneg g hg hA hB) (atom0692_nonneg g hg hA hB)) (add_nonneg (atom0693_nonneg g hg hA hB) (add_nonneg (atom0694_nonneg g hg hA hB) (atom0695_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0696_nonneg g hg hA hB) (atom0697_nonneg g hg hA hB)) (add_nonneg (atom0698_nonneg g hg hA hB) (add_nonneg (atom0699_nonneg g hg hA hB) (atom0700_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0701_nonneg g hg hA hB) (atom0702_nonneg g hg hA hB)) (add_nonneg (atom0703_nonneg g hg hA hB) (add_nonneg (atom0704_nonneg g hg hA hB) (atom0705_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0706_nonneg g hg hA hB) (atom0707_nonneg g hg hA hB)) (add_nonneg (atom0708_nonneg g hg hA hB) (add_nonneg (atom0709_nonneg g hg hA hB) (atom0710_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0711_nonneg g hg hA hB) (atom0712_nonneg g hg hA hB)) (add_nonneg (atom0713_nonneg g hg hA hB) (add_nonneg (atom0714_nonneg g hg hA hB) (atom0715_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0716_nonneg g hg hA hB) (atom0717_nonneg g hg hA hB)) (add_nonneg (atom0718_nonneg g hg hA hB) (add_nonneg (atom0719_nonneg g hg hA hB) (atom0720_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0721_nonneg g hg hA hB) (atom0722_nonneg g hg hA hB)) (add_nonneg (atom0723_nonneg g hg hA hB) (add_nonneg (atom0724_nonneg g hg hA hB) (atom0725_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0726_nonneg g hg hA hB) (atom0727_nonneg g hg hA hB)) (add_nonneg (atom0728_nonneg g hg hA hB) (add_nonneg (atom0729_nonneg g hg hA hB) (atom0730_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0731_nonneg g hg hA hB) (atom0732_nonneg g hg hA hB)) (add_nonneg (atom0733_nonneg g hg hA hB) (add_nonneg (atom0734_nonneg g hg hA hB) (atom0735_nonneg g hg hA hB))))))))

end APPT.Finite21
