import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0633 : SparsePolynomial.Poly := [([9,10,12], 1)]
theorem eval_atom0633 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0633 = ((g 9) * (g 10) * (g 12)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0633_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202089600 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634 : SparsePolynomial.Poly := [([9,10,13], 1)]
theorem eval_atom0634 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0634 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0634_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147225600 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom0635 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0635 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0635_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228441600 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom0636 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0636 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0636_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101130120 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637 : SparsePolynomial.Poly := [([9,11,12], 1)]
theorem eval_atom0637 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0637 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0637_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235482120 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638 : SparsePolynomial.Poly := [([9,11,13], 1)]
theorem eval_atom0638 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0638 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0638_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199784880 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom0639 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0639 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0639_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213034320 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom0640 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0640 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0640_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115344000 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom0641 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0641 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0641_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226886400 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom0642 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0642 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0642_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223084800 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom0643 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0643 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0643_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119750400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644 : SparsePolynomial.Poly := [([9,13,14], 1)]
theorem eval_atom0644 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0644 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0644_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (247622400 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom0645 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0645 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0645_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108864000 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom0646 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0646 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0646_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35465688 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647 : SparsePolynomial.Poly := [([10,10,12], 1)]
theorem eval_atom0647 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0647 = ((g 10) * (g 10) * (g 12)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0647_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83210112 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648 : SparsePolynomial.Poly := [([10,10,13], 1)]
theorem eval_atom0648 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0648 = ((g 10) * (g 10) * (g 13)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0648_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65111040 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649 : SparsePolynomial.Poly := [([10,10,14], 1)]
theorem eval_atom0649 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0649 = ((g 10) * (g 10) * (g 14)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0649_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101443968 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom0650 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0650 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0650_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77114160 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651 : SparsePolynomial.Poly := [([10,11,12], 1)]
theorem eval_atom0651 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0651 = ((g 10) * (g 11) * (g 12)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0651_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216736560 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652 : SparsePolynomial.Poly := [([10,11,13], 1)]
theorem eval_atom0652 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0652 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0652_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210325680 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653 : SparsePolynomial.Poly := [([10,11,14], 1)]
theorem eval_atom0653 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0653 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0653_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232889040 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom0654 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0654 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0654_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118713600 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655 : SparsePolynomial.Poly := [([10,12,13], 1)]
theorem eval_atom0655 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0655 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0655_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244131840 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656 : SparsePolynomial.Poly := [([10,12,14], 1)]
theorem eval_atom0656 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0656 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0656_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250836480 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom0657 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0657 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0657_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131725440 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom0658 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0658 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0658_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283271040 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom0659 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0659 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0659_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130636800 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom0660 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0660 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0660_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31014360 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661 : SparsePolynomial.Poly := [([11,11,12], 1)]
theorem eval_atom0661 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0661 = ((g 11) * (g 11) * (g 12)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0661_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108981720 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662 : SparsePolynomial.Poly := [([11,11,13], 1)]
theorem eval_atom0662 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0662 = ((g 11) * (g 11) * (g 13)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0662_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110433240 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663 : SparsePolynomial.Poly := [([11,11,14], 1)]
theorem eval_atom0663 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0663 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0663_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86427000 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664 : SparsePolynomial.Poly := [([11,12,12], 1)]
theorem eval_atom0664 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0664 = ((g 11) * (g 12) * (g 12)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0664_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122083200 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665 : SparsePolynomial.Poly := [([11,12,13], 1)]
theorem eval_atom0665 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0665 = ((g 11) * (g 12) * (g 13)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0665_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (261377280 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666 : SparsePolynomial.Poly := [([11,12,14], 1)]
theorem eval_atom0666 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0666 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0666_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198698400 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom0667 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0667 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0667_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143700480 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668 : SparsePolynomial.Poly := [([11,13,14], 1)]
theorem eval_atom0668 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0668 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0668_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (239029920 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom0669 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0669 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0669_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72519840 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom0670 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0670 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0670_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41817600 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671 : SparsePolynomial.Poly := [([12,12,13], 1)]
theorem eval_atom0671 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0671 = ((g 12) * (g 12) * (g 13)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0671_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139311360 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672 : SparsePolynomial.Poly := [([12,12,14], 1)]
theorem eval_atom0672 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0672 = ((g 12) * (g 12) * (g 14)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0672_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98737920 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom0673 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0673 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0673_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155675520 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674 : SparsePolynomial.Poly := [([12,13,14], 1)]
theorem eval_atom0674 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0674 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0674_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245704320 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom0675 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0675 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0675_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65318400 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676 : SparsePolynomial.Poly := [([13,13,13], 1)]
theorem eval_atom0676 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0676 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0676_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55883520 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677 : SparsePolynomial.Poly := [([13,13,14], 1)]
theorem eval_atom0677 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0677 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0677_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140676480 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom0678 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0678 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0678_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87091200 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block008 : SparsePolynomial.Poly := [([9,10,12], 202089600), ([9,10,13], 147225600), ([9,10,14], 228441600), ([9,11,11], 101130120), ([9,11,12], 235482120), ([9,11,13], 199784880), ([9,11,14], 213034320), ([9,12,12], 115344000), ([9,12,13], 226886400), ([9,12,14], 223084800), ([9,13,13], 119750400), ([9,13,14], 247622400), ([9,14,14], 108864000), ([10,10,11], 35465688), ([10,10,12], 83210112), ([10,10,13], 65111040), ([10,10,14], 101443968), ([10,11,11], 77114160), ([10,11,12], 216736560), ([10,11,13], 210325680), ([10,11,14], 232889040), ([10,12,12], 118713600), ([10,12,13], 244131840), ([10,12,14], 250836480), ([10,13,13], 131725440), ([10,13,14], 283271040), ([10,14,14], 130636800), ([11,11,11], 31014360), ([11,11,12], 108981720), ([11,11,13], 110433240), ([11,11,14], 86427000), ([11,12,12], 122083200), ([11,12,13], 261377280), ([11,12,14], 198698400), ([11,13,13], 143700480), ([11,13,14], 239029920), ([11,14,14], 72519840), ([12,12,12], 41817600), ([12,12,13], 139311360), ([12,12,14], 98737920), ([12,13,13], 155675520), ([12,13,14], 245704320), ([12,14,14], 65318400), ([13,13,13], 55883520), ([13,13,14], 140676480), ([13,14,14], 87091200)]
theorem block008_data : block008 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (202089600 : Int) atom0633) (SparsePolynomial.scale (147225600 : Int) atom0634)) (SparsePolynomial.merge (SparsePolynomial.scale (228441600 : Int) atom0635) (SparsePolynomial.merge (SparsePolynomial.scale (101130120 : Int) atom0636) (SparsePolynomial.scale (235482120 : Int) atom0637)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (199784880 : Int) atom0638) (SparsePolynomial.merge (SparsePolynomial.scale (213034320 : Int) atom0639) (SparsePolynomial.scale (115344000 : Int) atom0640))) (SparsePolynomial.merge (SparsePolynomial.scale (226886400 : Int) atom0641) (SparsePolynomial.merge (SparsePolynomial.scale (223084800 : Int) atom0642) (SparsePolynomial.scale (119750400 : Int) atom0643))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (247622400 : Int) atom0644) (SparsePolynomial.merge (SparsePolynomial.scale (108864000 : Int) atom0645) (SparsePolynomial.scale (35465688 : Int) atom0646))) (SparsePolynomial.merge (SparsePolynomial.scale (83210112 : Int) atom0647) (SparsePolynomial.merge (SparsePolynomial.scale (65111040 : Int) atom0648) (SparsePolynomial.scale (101443968 : Int) atom0649)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (77114160 : Int) atom0650) (SparsePolynomial.merge (SparsePolynomial.scale (216736560 : Int) atom0651) (SparsePolynomial.scale (210325680 : Int) atom0652))) (SparsePolynomial.merge (SparsePolynomial.scale (232889040 : Int) atom0653) (SparsePolynomial.merge (SparsePolynomial.scale (118713600 : Int) atom0654) (SparsePolynomial.scale (244131840 : Int) atom0655)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (250836480 : Int) atom0656) (SparsePolynomial.scale (131725440 : Int) atom0657)) (SparsePolynomial.merge (SparsePolynomial.scale (283271040 : Int) atom0658) (SparsePolynomial.merge (SparsePolynomial.scale (130636800 : Int) atom0659) (SparsePolynomial.scale (31014360 : Int) atom0660)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (108981720 : Int) atom0661) (SparsePolynomial.merge (SparsePolynomial.scale (110433240 : Int) atom0662) (SparsePolynomial.scale (86427000 : Int) atom0663))) (SparsePolynomial.merge (SparsePolynomial.scale (122083200 : Int) atom0664) (SparsePolynomial.merge (SparsePolynomial.scale (261377280 : Int) atom0665) (SparsePolynomial.scale (198698400 : Int) atom0666))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (143700480 : Int) atom0667) (SparsePolynomial.merge (SparsePolynomial.scale (239029920 : Int) atom0668) (SparsePolynomial.scale (72519840 : Int) atom0669))) (SparsePolynomial.merge (SparsePolynomial.scale (41817600 : Int) atom0670) (SparsePolynomial.merge (SparsePolynomial.scale (139311360 : Int) atom0671) (SparsePolynomial.scale (98737920 : Int) atom0672)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (155675520 : Int) atom0673) (SparsePolynomial.merge (SparsePolynomial.scale (245704320 : Int) atom0674) (SparsePolynomial.scale (65318400 : Int) atom0675))) (SparsePolynomial.merge (SparsePolynomial.scale (55883520 : Int) atom0676) (SparsePolynomial.merge (SparsePolynomial.scale (140676480 : Int) atom0677) (SparsePolynomial.scale (87091200 : Int) atom0678))))))) := by decide +kernel
theorem block008_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block008 := by
  rw [block008_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0633_nonneg g hg hA hB) (atom0634_nonneg g hg hA hB)) (add_nonneg (atom0635_nonneg g hg hA hB) (add_nonneg (atom0636_nonneg g hg hA hB) (atom0637_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0638_nonneg g hg hA hB) (add_nonneg (atom0639_nonneg g hg hA hB) (atom0640_nonneg g hg hA hB))) (add_nonneg (atom0641_nonneg g hg hA hB) (add_nonneg (atom0642_nonneg g hg hA hB) (atom0643_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0644_nonneg g hg hA hB) (add_nonneg (atom0645_nonneg g hg hA hB) (atom0646_nonneg g hg hA hB))) (add_nonneg (atom0647_nonneg g hg hA hB) (add_nonneg (atom0648_nonneg g hg hA hB) (atom0649_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0650_nonneg g hg hA hB) (add_nonneg (atom0651_nonneg g hg hA hB) (atom0652_nonneg g hg hA hB))) (add_nonneg (atom0653_nonneg g hg hA hB) (add_nonneg (atom0654_nonneg g hg hA hB) (atom0655_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0656_nonneg g hg hA hB) (atom0657_nonneg g hg hA hB)) (add_nonneg (atom0658_nonneg g hg hA hB) (add_nonneg (atom0659_nonneg g hg hA hB) (atom0660_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0661_nonneg g hg hA hB) (add_nonneg (atom0662_nonneg g hg hA hB) (atom0663_nonneg g hg hA hB))) (add_nonneg (atom0664_nonneg g hg hA hB) (add_nonneg (atom0665_nonneg g hg hA hB) (atom0666_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0667_nonneg g hg hA hB) (add_nonneg (atom0668_nonneg g hg hA hB) (atom0669_nonneg g hg hA hB))) (add_nonneg (atom0670_nonneg g hg hA hB) (add_nonneg (atom0671_nonneg g hg hA hB) (atom0672_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0673_nonneg g hg hA hB) (add_nonneg (atom0674_nonneg g hg hA hB) (atom0675_nonneg g hg hA hB))) (add_nonneg (atom0676_nonneg g hg hA hB) (add_nonneg (atom0677_nonneg g hg hA hB) (atom0678_nonneg g hg hA hB)))))))

end APPT.Finite15
