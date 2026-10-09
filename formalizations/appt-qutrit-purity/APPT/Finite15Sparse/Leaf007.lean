import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0553 : SparsePolynomial.Poly := [([6,9,10], 1)]
theorem eval_atom0553 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60699240 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554 : SparsePolynomial.Poly := [([6,9,11], 1)]
theorem eval_atom0554 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126096480 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555 : SparsePolynomial.Poly := [([6,9,12], 1)]
theorem eval_atom0555 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156091320 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556 : SparsePolynomial.Poly := [([6,9,13], 1)]
theorem eval_atom0556 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110217240 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557 : SparsePolynomial.Poly := [([6,9,14], 1)]
theorem eval_atom0557 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (200423160 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom0558 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26469504 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559 : SparsePolynomial.Poly := [([6,10,11], 1)]
theorem eval_atom0559 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100582560 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560 : SparsePolynomial.Poly := [([6,10,12], 1)]
theorem eval_atom0560 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147665700 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561 : SparsePolynomial.Poly := [([6,10,13], 1)]
theorem eval_atom0561 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118586160 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562 : SparsePolynomial.Poly := [([6,10,14], 1)]
theorem eval_atom0562 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173295990 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom0563 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86044680 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564 : SparsePolynomial.Poly := [([6,11,12], 1)]
theorem eval_atom0564 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170421840 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565 : SparsePolynomial.Poly := [([6,11,13], 1)]
theorem eval_atom0565 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146729880 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566 : SparsePolynomial.Poly := [([6,11,14], 1)]
theorem eval_atom0566 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224658360 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567 : SparsePolynomial.Poly := [([6,12,12], 1)]
theorem eval_atom0567 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67597740 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568 : SparsePolynomial.Poly := [([6,12,13], 1)]
theorem eval_atom0568 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129105900 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569 : SparsePolynomial.Poly := [([6,12,14], 1)]
theorem eval_atom0569 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220009230 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570 : SparsePolynomial.Poly := [([6,13,13], 1)]
theorem eval_atom0570 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40960080 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571 : SparsePolynomial.Poly := [([6,13,14], 1)]
theorem eval_atom0571 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183914010 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572 : SparsePolynomial.Poly := [([6,14,14], 1)]
theorem eval_atom0572 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132831090 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom0573 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13440 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom0574 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2284800 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575 : SparsePolynomial.Poly := [([7,8,10], 1)]
theorem eval_atom0575 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0575 = ((g 7) * (g 8) * (g 10)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0575_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (509120 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576 : SparsePolynomial.Poly := [([7,8,11], 1)]
theorem eval_atom0576 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0576 = ((g 7) * (g 8) * (g 11)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0576_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11378240 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577 : SparsePolynomial.Poly := [([7,8,12], 1)]
theorem eval_atom0577 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0577 = ((g 7) * (g 8) * (g 12)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0577_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26440640 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578 : SparsePolynomial.Poly := [([7,8,13], 1)]
theorem eval_atom0578 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0578 = ((g 7) * (g 8) * (g 13)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0578_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33900480 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579 : SparsePolynomial.Poly := [([7,8,14], 1)]
theorem eval_atom0579 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0579 = ((g 7) * (g 8) * (g 14)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0579_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83671920 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom0580 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0580 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0580_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14717760 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581 : SparsePolynomial.Poly := [([7,9,10], 1)]
theorem eval_atom0581 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0581 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0581_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37833600 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582 : SparsePolynomial.Poly := [([7,9,11], 1)]
theorem eval_atom0582 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0582 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0582_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108389280 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583 : SparsePolynomial.Poly := [([7,9,12], 1)]
theorem eval_atom0583 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0583 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0583_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140625120 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584 : SparsePolynomial.Poly := [([7,9,13], 1)]
theorem eval_atom0584 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0584 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0584_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98938560 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585 : SparsePolynomial.Poly := [([7,9,14], 1)]
theorem eval_atom0585 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0585 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0585_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193577040 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom0586 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0586 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0586_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16205184 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom0587 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0587 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0587_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87384840 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588 : SparsePolynomial.Poly := [([7,10,12], 1)]
theorem eval_atom0588 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0588 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0588_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142194240 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589 : SparsePolynomial.Poly := [([7,10,13], 1)]
theorem eval_atom0589 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0589 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0589_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120840960 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590 : SparsePolynomial.Poly := [([7,10,14], 1)]
theorem eval_atom0590 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0590 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0590_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183474720 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom0591 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0591 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0591_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82001160 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592 : SparsePolynomial.Poly := [([7,11,12], 1)]
theorem eval_atom0592 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0592 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0592_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175846920 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593 : SparsePolynomial.Poly := [([7,11,13], 1)]
theorem eval_atom0593 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0593 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0593_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163720560 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594 : SparsePolynomial.Poly := [([7,11,14], 1)]
theorem eval_atom0594 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0594 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0594_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253214640 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595 : SparsePolynomial.Poly := [([7,12,12], 1)]
theorem eval_atom0595 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0595 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0595_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77264640 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596 : SparsePolynomial.Poly := [([7,12,13], 1)]
theorem eval_atom0596 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0596 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0596_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164422560 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597 : SparsePolynomial.Poly := [([7,12,14], 1)]
theorem eval_atom0597 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0597 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0597_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270259200 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598 : SparsePolynomial.Poly := [([7,13,13], 1)]
theorem eval_atom0598 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0598 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0598_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65834880 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599 : SparsePolynomial.Poly := [([7,13,14], 1)]
theorem eval_atom0599 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0599 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0599_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (251478000 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600 : SparsePolynomial.Poly := [([7,14,14], 1)]
theorem eval_atom0600 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0600 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0600_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174182400 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom0601 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0601 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0601_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3436560 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602 : SparsePolynomial.Poly := [([8,8,12], 1)]
theorem eval_atom0602 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0602 = ((g 8) * (g 8) * (g 12)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0602_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8981280 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603 : SparsePolynomial.Poly := [([8,8,14], 1)]
theorem eval_atom0603 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0603 = ((g 8) * (g 8) * (g 14)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0603_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30443040 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom0604 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0604 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0604_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3985200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom0605 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0605 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0605_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14832720 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606 : SparsePolynomial.Poly := [([8,9,11], 1)]
theorem eval_atom0606 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0606 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0606_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87102000 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607 : SparsePolynomial.Poly := [([8,9,12], 1)]
theorem eval_atom0607 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0607 = ((g 8) * (g 9) * (g 12)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0607_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121237560 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608 : SparsePolynomial.Poly := [([8,9,13], 1)]
theorem eval_atom0608 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0608 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0608_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75718800 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom0609 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0609 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0609_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187377300 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom0610 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0610 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0610_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5940864 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom0611 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0611 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0611_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74322360 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom0612 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0612 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0612_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136925640 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613 : SparsePolynomial.Poly := [([8,10,13], 1)]
theorem eval_atom0613 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0613 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0613_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123366240 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom0614 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0614 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0614_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193957740 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom0615 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0615 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0615_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77957640 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom0616 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0616 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0616_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179823240 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom0617 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0617 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0617_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185492160 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom0618 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0618 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0618_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273069360 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom0619 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0619 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0619_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84758400 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom0620 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0620 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0620_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204013080 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom0621 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0621 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0621_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (304197120 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom0622 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0622 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0622_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100271520 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom0623 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0623 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0623_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312395940 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom0624 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0624 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0624_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195955200 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom0625 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0625 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0625_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3456000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom0626 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0626 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0626_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17798400 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627 : SparsePolynomial.Poly := [([9,9,11], 1)]
theorem eval_atom0627 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0627 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0627_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65173680 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628 : SparsePolynomial.Poly := [([9,9,12], 1)]
theorem eval_atom0628 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0628 = ((g 9) * (g 9) * (g 12)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0628_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87091200 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629 : SparsePolynomial.Poly := [([9,9,13], 1)]
theorem eval_atom0629 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0629 = ((g 9) * (g 9) * (g 13)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0629_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40089600 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630 : SparsePolynomial.Poly := [([9,9,14], 1)]
theorem eval_atom0630 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0630 = ((g 9) * (g 9) * (g 14)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0630_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101952000 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom0631 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0631 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0631_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20808576 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632 : SparsePolynomial.Poly := [([9,10,11], 1)]
theorem eval_atom0632 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0632 = ((g 9) * (g 10) * (g 11)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0632_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126358920 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block007 : SparsePolynomial.Poly := [([6,9,10], 60699240), ([6,9,11], 126096480), ([6,9,12], 156091320), ([6,9,13], 110217240), ([6,9,14], 200423160), ([6,10,10], 26469504), ([6,10,11], 100582560), ([6,10,12], 147665700), ([6,10,13], 118586160), ([6,10,14], 173295990), ([6,11,11], 86044680), ([6,11,12], 170421840), ([6,11,13], 146729880), ([6,11,14], 224658360), ([6,12,12], 67597740), ([6,12,13], 129105900), ([6,12,14], 220009230), ([6,13,13], 40960080), ([6,13,14], 183914010), ([6,14,14], 132831090), ([7,7,7], 13440), ([7,8,8], 2284800), ([7,8,10], 509120), ([7,8,11], 11378240), ([7,8,12], 26440640), ([7,8,13], 33900480), ([7,8,14], 83671920), ([7,9,9], 14717760), ([7,9,10], 37833600), ([7,9,11], 108389280), ([7,9,12], 140625120), ([7,9,13], 98938560), ([7,9,14], 193577040), ([7,10,10], 16205184), ([7,10,11], 87384840), ([7,10,12], 142194240), ([7,10,13], 120840960), ([7,10,14], 183474720), ([7,11,11], 82001160), ([7,11,12], 175846920), ([7,11,13], 163720560), ([7,11,14], 253214640), ([7,12,12], 77264640), ([7,12,13], 164422560), ([7,12,14], 270259200), ([7,13,13], 65834880), ([7,13,14], 251478000), ([7,14,14], 174182400), ([8,8,11], 3436560), ([8,8,12], 8981280), ([8,8,14], 30443040), ([8,9,9], 3985200), ([8,9,10], 14832720), ([8,9,11], 87102000), ([8,9,12], 121237560), ([8,9,13], 75718800), ([8,9,14], 187377300), ([8,10,10], 5940864), ([8,10,11], 74322360), ([8,10,12], 136925640), ([8,10,13], 123366240), ([8,10,14], 193957740), ([8,11,11], 77957640), ([8,11,12], 179823240), ([8,11,13], 185492160), ([8,11,14], 273069360), ([8,12,12], 84758400), ([8,12,13], 204013080), ([8,12,14], 304197120), ([8,13,13], 100271520), ([8,13,14], 312395940), ([8,14,14], 195955200), ([9,9,9], 3456000), ([9,9,10], 17798400), ([9,9,11], 65173680), ([9,9,12], 87091200), ([9,9,13], 40089600), ([9,9,14], 101952000), ([9,10,10], 20808576), ([9,10,11], 126358920)]
theorem block007_data : block007 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (60699240 : Int) atom0553) (SparsePolynomial.scale (126096480 : Int) atom0554)) (SparsePolynomial.merge (SparsePolynomial.scale (156091320 : Int) atom0555) (SparsePolynomial.merge (SparsePolynomial.scale (110217240 : Int) atom0556) (SparsePolynomial.scale (200423160 : Int) atom0557)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26469504 : Int) atom0558) (SparsePolynomial.scale (100582560 : Int) atom0559)) (SparsePolynomial.merge (SparsePolynomial.scale (147665700 : Int) atom0560) (SparsePolynomial.merge (SparsePolynomial.scale (118586160 : Int) atom0561) (SparsePolynomial.scale (173295990 : Int) atom0562))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (86044680 : Int) atom0563) (SparsePolynomial.scale (170421840 : Int) atom0564)) (SparsePolynomial.merge (SparsePolynomial.scale (146729880 : Int) atom0565) (SparsePolynomial.merge (SparsePolynomial.scale (224658360 : Int) atom0566) (SparsePolynomial.scale (67597740 : Int) atom0567)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (129105900 : Int) atom0568) (SparsePolynomial.scale (220009230 : Int) atom0569)) (SparsePolynomial.merge (SparsePolynomial.scale (40960080 : Int) atom0570) (SparsePolynomial.merge (SparsePolynomial.scale (183914010 : Int) atom0571) (SparsePolynomial.scale (132831090 : Int) atom0572)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13440 : Int) atom0573) (SparsePolynomial.scale (2284800 : Int) atom0574)) (SparsePolynomial.merge (SparsePolynomial.scale (509120 : Int) atom0575) (SparsePolynomial.merge (SparsePolynomial.scale (11378240 : Int) atom0576) (SparsePolynomial.scale (26440640 : Int) atom0577)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (33900480 : Int) atom0578) (SparsePolynomial.scale (83671920 : Int) atom0579)) (SparsePolynomial.merge (SparsePolynomial.scale (14717760 : Int) atom0580) (SparsePolynomial.merge (SparsePolynomial.scale (37833600 : Int) atom0581) (SparsePolynomial.scale (108389280 : Int) atom0582))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (140625120 : Int) atom0583) (SparsePolynomial.scale (98938560 : Int) atom0584)) (SparsePolynomial.merge (SparsePolynomial.scale (193577040 : Int) atom0585) (SparsePolynomial.merge (SparsePolynomial.scale (16205184 : Int) atom0586) (SparsePolynomial.scale (87384840 : Int) atom0587)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142194240 : Int) atom0588) (SparsePolynomial.scale (120840960 : Int) atom0589)) (SparsePolynomial.merge (SparsePolynomial.scale (183474720 : Int) atom0590) (SparsePolynomial.merge (SparsePolynomial.scale (82001160 : Int) atom0591) (SparsePolynomial.scale (175846920 : Int) atom0592))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (163720560 : Int) atom0593) (SparsePolynomial.scale (253214640 : Int) atom0594)) (SparsePolynomial.merge (SparsePolynomial.scale (77264640 : Int) atom0595) (SparsePolynomial.merge (SparsePolynomial.scale (164422560 : Int) atom0596) (SparsePolynomial.scale (270259200 : Int) atom0597)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (65834880 : Int) atom0598) (SparsePolynomial.scale (251478000 : Int) atom0599)) (SparsePolynomial.merge (SparsePolynomial.scale (174182400 : Int) atom0600) (SparsePolynomial.merge (SparsePolynomial.scale (3436560 : Int) atom0601) (SparsePolynomial.scale (8981280 : Int) atom0602))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30443040 : Int) atom0603) (SparsePolynomial.scale (3985200 : Int) atom0604)) (SparsePolynomial.merge (SparsePolynomial.scale (14832720 : Int) atom0605) (SparsePolynomial.merge (SparsePolynomial.scale (87102000 : Int) atom0606) (SparsePolynomial.scale (121237560 : Int) atom0607)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (75718800 : Int) atom0608) (SparsePolynomial.scale (187377300 : Int) atom0609)) (SparsePolynomial.merge (SparsePolynomial.scale (5940864 : Int) atom0610) (SparsePolynomial.merge (SparsePolynomial.scale (74322360 : Int) atom0611) (SparsePolynomial.scale (136925640 : Int) atom0612)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (123366240 : Int) atom0613) (SparsePolynomial.scale (193957740 : Int) atom0614)) (SparsePolynomial.merge (SparsePolynomial.scale (77957640 : Int) atom0615) (SparsePolynomial.merge (SparsePolynomial.scale (179823240 : Int) atom0616) (SparsePolynomial.scale (185492160 : Int) atom0617)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (273069360 : Int) atom0618) (SparsePolynomial.scale (84758400 : Int) atom0619)) (SparsePolynomial.merge (SparsePolynomial.scale (204013080 : Int) atom0620) (SparsePolynomial.merge (SparsePolynomial.scale (304197120 : Int) atom0621) (SparsePolynomial.scale (100271520 : Int) atom0622))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (312395940 : Int) atom0623) (SparsePolynomial.scale (195955200 : Int) atom0624)) (SparsePolynomial.merge (SparsePolynomial.scale (3456000 : Int) atom0625) (SparsePolynomial.merge (SparsePolynomial.scale (17798400 : Int) atom0626) (SparsePolynomial.scale (65173680 : Int) atom0627)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (87091200 : Int) atom0628) (SparsePolynomial.scale (40089600 : Int) atom0629)) (SparsePolynomial.merge (SparsePolynomial.scale (101952000 : Int) atom0630) (SparsePolynomial.merge (SparsePolynomial.scale (20808576 : Int) atom0631) (SparsePolynomial.scale (126358920 : Int) atom0632)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block007 := by
  rw [block007_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0553_nonneg g hg hA hB) (atom0554_nonneg g hg hA hB)) (add_nonneg (atom0555_nonneg g hg hA hB) (add_nonneg (atom0556_nonneg g hg hA hB) (atom0557_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0558_nonneg g hg hA hB) (atom0559_nonneg g hg hA hB)) (add_nonneg (atom0560_nonneg g hg hA hB) (add_nonneg (atom0561_nonneg g hg hA hB) (atom0562_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0563_nonneg g hg hA hB) (atom0564_nonneg g hg hA hB)) (add_nonneg (atom0565_nonneg g hg hA hB) (add_nonneg (atom0566_nonneg g hg hA hB) (atom0567_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0568_nonneg g hg hA hB) (atom0569_nonneg g hg hA hB)) (add_nonneg (atom0570_nonneg g hg hA hB) (add_nonneg (atom0571_nonneg g hg hA hB) (atom0572_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0573_nonneg g hg hA hB) (atom0574_nonneg g hg hA hB)) (add_nonneg (atom0575_nonneg g hg hA hB) (add_nonneg (atom0576_nonneg g hg hA hB) (atom0577_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0578_nonneg g hg hA hB) (atom0579_nonneg g hg hA hB)) (add_nonneg (atom0580_nonneg g hg hA hB) (add_nonneg (atom0581_nonneg g hg hA hB) (atom0582_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0583_nonneg g hg hA hB) (atom0584_nonneg g hg hA hB)) (add_nonneg (atom0585_nonneg g hg hA hB) (add_nonneg (atom0586_nonneg g hg hA hB) (atom0587_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0588_nonneg g hg hA hB) (atom0589_nonneg g hg hA hB)) (add_nonneg (atom0590_nonneg g hg hA hB) (add_nonneg (atom0591_nonneg g hg hA hB) (atom0592_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0593_nonneg g hg hA hB) (atom0594_nonneg g hg hA hB)) (add_nonneg (atom0595_nonneg g hg hA hB) (add_nonneg (atom0596_nonneg g hg hA hB) (atom0597_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0598_nonneg g hg hA hB) (atom0599_nonneg g hg hA hB)) (add_nonneg (atom0600_nonneg g hg hA hB) (add_nonneg (atom0601_nonneg g hg hA hB) (atom0602_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0603_nonneg g hg hA hB) (atom0604_nonneg g hg hA hB)) (add_nonneg (atom0605_nonneg g hg hA hB) (add_nonneg (atom0606_nonneg g hg hA hB) (atom0607_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0608_nonneg g hg hA hB) (atom0609_nonneg g hg hA hB)) (add_nonneg (atom0610_nonneg g hg hA hB) (add_nonneg (atom0611_nonneg g hg hA hB) (atom0612_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0613_nonneg g hg hA hB) (atom0614_nonneg g hg hA hB)) (add_nonneg (atom0615_nonneg g hg hA hB) (add_nonneg (atom0616_nonneg g hg hA hB) (atom0617_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0618_nonneg g hg hA hB) (atom0619_nonneg g hg hA hB)) (add_nonneg (atom0620_nonneg g hg hA hB) (add_nonneg (atom0621_nonneg g hg hA hB) (atom0622_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0623_nonneg g hg hA hB) (atom0624_nonneg g hg hA hB)) (add_nonneg (atom0625_nonneg g hg hA hB) (add_nonneg (atom0626_nonneg g hg hA hB) (atom0627_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0628_nonneg g hg hA hB) (atom0629_nonneg g hg hA hB)) (add_nonneg (atom0630_nonneg g hg hA hB) (add_nonneg (atom0631_nonneg g hg hA hB) (atom0632_nonneg g hg hA hB))))))))

end APPT.Finite15
