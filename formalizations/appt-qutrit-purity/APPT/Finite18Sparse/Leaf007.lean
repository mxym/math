import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0495 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0495 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0495 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0495_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3718671360 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0496 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0496 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0496_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6793720320 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0497 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0497 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0497_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6517608960 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0498 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0498 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0498_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6167040000 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0499 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0499 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0499_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7979381760 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0500 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0500 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0500_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6566323200 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0501 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0501 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0501_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8933124000 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502 : SparsePolynomial.Poly := [([2,8,15], 1)]
theorem eval_atom0502 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0502 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0502_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7949368320 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503 : SparsePolynomial.Poly := [([2,8,16], 1)]
theorem eval_atom0503 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0503 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0503_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8692055040 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504 : SparsePolynomial.Poly := [([2,8,17], 1)]
theorem eval_atom0504 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0504 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0504_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10609182720 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0505 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0505 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0505_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4164011520 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0506 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0506 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0506_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7503144960 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0507 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0507 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0507_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6954524160 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0508 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0508 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0508_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8592628800 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0509 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0509 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0509_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7029147840 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0510 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0510 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0510_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9631143840 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511 : SparsePolynomial.Poly := [([2,9,15], 1)]
theorem eval_atom0511 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0511 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0511_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8158977600 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512 : SparsePolynomial.Poly := [([2,9,16], 1)]
theorem eval_atom0512 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0512 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0512_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8798871360 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513 : SparsePolynomial.Poly := [([2,9,17], 1)]
theorem eval_atom0513 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0513 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0513_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10613206080 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0514 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0514 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0514_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4531960320 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0515 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0515 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0515_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7932940800 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0516 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0516 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0516_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9311655360 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517 : SparsePolynomial.Poly := [([2,10,13], 1)]
theorem eval_atom0517 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0517 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0517_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7477765440 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518 : SparsePolynomial.Poly := [([2,10,14], 1)]
theorem eval_atom0518 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0518 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0518_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10379483040 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519 : SparsePolynomial.Poly := [([2,10,15], 1)]
theorem eval_atom0519 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0519 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0519_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8044739520 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520 : SparsePolynomial.Poly := [([2,10,16], 1)]
theorem eval_atom0520 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0520 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0520_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8392186560 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521 : SparsePolynomial.Poly := [([2,10,17], 1)]
theorem eval_atom0521 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0521 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0521_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10204830720 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0522 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0522 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0522_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4927426560 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523 : SparsePolynomial.Poly := [([2,11,12], 1)]
theorem eval_atom0523 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0523 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0523_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9870336000 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524 : SparsePolynomial.Poly := [([2,11,13], 1)]
theorem eval_atom0524 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0524 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0524_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7722086400 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525 : SparsePolynomial.Poly := [([2,11,14], 1)]
theorem eval_atom0525 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0525 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0525_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10978907040 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526 : SparsePolynomial.Poly := [([2,11,15], 1)]
theorem eval_atom0526 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0526 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0526_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8678154240 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527 : SparsePolynomial.Poly := [([2,11,16], 1)]
theorem eval_atom0527 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0527 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0527_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7662090240 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528 : SparsePolynomial.Poly := [([2,11,17], 1)]
theorem eval_atom0528 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0528 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0528_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11373788160 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529 : SparsePolynomial.Poly := [([2,12,12], 1)]
theorem eval_atom0529 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0529 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0529_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6543452160 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530 : SparsePolynomial.Poly := [([2,12,13], 1)]
theorem eval_atom0530 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0530 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0530_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10721894400 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531 : SparsePolynomial.Poly := [([2,12,14], 1)]
theorem eval_atom0531 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0531 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0531_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15248311200 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532 : SparsePolynomial.Poly := [([2,12,15], 1)]
theorem eval_atom0532 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0532 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0532_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13098516480 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533 : SparsePolynomial.Poly := [([2,12,16], 1)]
theorem eval_atom0533 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0533 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0533_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7930137600 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534 : SparsePolynomial.Poly := [([2,12,17], 1)]
theorem eval_atom0534 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0534 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0534_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12465129600 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535 : SparsePolynomial.Poly := [([2,13,13], 1)]
theorem eval_atom0535 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0535 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0535_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4665765888 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536 : SparsePolynomial.Poly := [([2,13,14], 1)]
theorem eval_atom0536 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0536 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0536_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12464877240 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537 : SparsePolynomial.Poly := [([2,13,15], 1)]
theorem eval_atom0537 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0537 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0537_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12188897280 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538 : SparsePolynomial.Poly := [([2,13,16], 1)]
theorem eval_atom0538 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0538 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0538_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8198184960 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539 : SparsePolynomial.Poly := [([2,13,17], 1)]
theorem eval_atom0539 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0539 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0539_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9925534080 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540 : SparsePolynomial.Poly := [([2,14,14], 1)]
theorem eval_atom0540 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0540 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0540_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8286435000 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541 : SparsePolynomial.Poly := [([2,14,15], 1)]
theorem eval_atom0541 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0541 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0541_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12894527160 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542 : SparsePolynomial.Poly := [([2,14,16], 1)]
theorem eval_atom0542 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0542 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0542_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8358624720 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543 : SparsePolynomial.Poly := [([2,14,17], 1)]
theorem eval_atom0543 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0543 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0543_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10676419920 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544 : SparsePolynomial.Poly := [([2,15,15], 1)]
theorem eval_atom0544 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0544 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0544_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4296499200 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545 : SparsePolynomial.Poly := [([2,15,16], 1)]
theorem eval_atom0545 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0545 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0545_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5555934720 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546 : SparsePolynomial.Poly := [([2,15,17], 1)]
theorem eval_atom0546 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0546 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0546_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8244432000 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547 : SparsePolynomial.Poly := [([2,16,16], 1)]
theorem eval_atom0547 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0547 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0547_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (572866560 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548 : SparsePolynomial.Poly := [([2,16,17], 1)]
theorem eval_atom0548 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0548 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0548_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3862212480 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549 : SparsePolynomial.Poly := [([2,17,17], 1)]
theorem eval_atom0549 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0549 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0549_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2854776960 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0550 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0550 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0550_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249016320 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0551 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0551 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0551_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (633507840 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0552 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0552 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0552_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (519966720 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0553 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0553 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0553_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (406425600 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0554 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0554 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0554_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (292884480 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0555 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0555 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0555_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230576640 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom0556 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0556 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0556_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108003840 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557 : SparsePolynomial.Poly := [([3,3,10], 1)]
theorem eval_atom0557 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0557 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0557_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10590720 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558 : SparsePolynomial.Poly := [([3,3,12], 1)]
theorem eval_atom0558 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0558 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0558_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1501839360 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559 : SparsePolynomial.Poly := [([3,3,14], 1)]
theorem eval_atom0559 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0559 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0559_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1167149520 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0560 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0560 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0560_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1344806400 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0561 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0561 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0561_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1764439680 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0562 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0562 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0562_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (766439040 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0563 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0563 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0563_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (245414400 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0564 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0564 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0564_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (208266240 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom0565 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0565 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0565_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164398080 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom0566 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0566 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0566_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170849280 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom0567 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0567 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0567_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264122880 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom0568 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0568 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0568_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3555901440 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom0569 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0569 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0569_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (936962880 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom0570 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0570 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0570_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3289076640 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571 : SparsePolynomial.Poly := [([3,4,15], 1)]
theorem eval_atom0571 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0571 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0571_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2074914240 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572 : SparsePolynomial.Poly := [([3,4,16], 1)]
theorem eval_atom0572 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0572 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0572_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2798927040 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573 : SparsePolynomial.Poly := [([3,4,17], 1)]
theorem eval_atom0573 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0573 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0573_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3522939840 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0574 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0574 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0574_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1300867200 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block007 : SparsePolynomial.Poly := [([2,8,8], 3718671360), ([2,8,9], 6793720320), ([2,8,10], 6517608960), ([2,8,11], 6167040000), ([2,8,12], 7979381760), ([2,8,13], 6566323200), ([2,8,14], 8933124000), ([2,8,15], 7949368320), ([2,8,16], 8692055040), ([2,8,17], 10609182720), ([2,9,9], 4164011520), ([2,9,10], 7503144960), ([2,9,11], 6954524160), ([2,9,12], 8592628800), ([2,9,13], 7029147840), ([2,9,14], 9631143840), ([2,9,15], 8158977600), ([2,9,16], 8798871360), ([2,9,17], 10613206080), ([2,10,10], 4531960320), ([2,10,11], 7932940800), ([2,10,12], 9311655360), ([2,10,13], 7477765440), ([2,10,14], 10379483040), ([2,10,15], 8044739520), ([2,10,16], 8392186560), ([2,10,17], 10204830720), ([2,11,11], 4927426560), ([2,11,12], 9870336000), ([2,11,13], 7722086400), ([2,11,14], 10978907040), ([2,11,15], 8678154240), ([2,11,16], 7662090240), ([2,11,17], 11373788160), ([2,12,12], 6543452160), ([2,12,13], 10721894400), ([2,12,14], 15248311200), ([2,12,15], 13098516480), ([2,12,16], 7930137600), ([2,12,17], 12465129600), ([2,13,13], 4665765888), ([2,13,14], 12464877240), ([2,13,15], 12188897280), ([2,13,16], 8198184960), ([2,13,17], 9925534080), ([2,14,14], 8286435000), ([2,14,15], 12894527160), ([2,14,16], 8358624720), ([2,14,17], 10676419920), ([2,15,15], 4296499200), ([2,15,16], 5555934720), ([2,15,17], 8244432000), ([2,16,16], 572866560), ([2,16,17], 3862212480), ([2,17,17], 2854776960), ([3,3,3], 249016320), ([3,3,4], 633507840), ([3,3,5], 519966720), ([3,3,6], 406425600), ([3,3,7], 292884480), ([3,3,8], 230576640), ([3,3,9], 108003840), ([3,3,10], 10590720), ([3,3,12], 1501839360), ([3,3,14], 1167149520), ([3,4,4], 1344806400), ([3,4,5], 1764439680), ([3,4,6], 766439040), ([3,4,7], 245414400), ([3,4,8], 208266240), ([3,4,9], 164398080), ([3,4,10], 170849280), ([3,4,11], 264122880), ([3,4,12], 3555901440), ([3,4,13], 936962880), ([3,4,14], 3289076640), ([3,4,15], 2074914240), ([3,4,16], 2798927040), ([3,4,17], 3522939840), ([3,5,5], 1300867200)]
theorem block007_data : block007 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3718671360 : Int) atom0495) (SparsePolynomial.scale (6793720320 : Int) atom0496)) (SparsePolynomial.merge (SparsePolynomial.scale (6517608960 : Int) atom0497) (SparsePolynomial.merge (SparsePolynomial.scale (6167040000 : Int) atom0498) (SparsePolynomial.scale (7979381760 : Int) atom0499)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6566323200 : Int) atom0500) (SparsePolynomial.scale (8933124000 : Int) atom0501)) (SparsePolynomial.merge (SparsePolynomial.scale (7949368320 : Int) atom0502) (SparsePolynomial.merge (SparsePolynomial.scale (8692055040 : Int) atom0503) (SparsePolynomial.scale (10609182720 : Int) atom0504))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4164011520 : Int) atom0505) (SparsePolynomial.scale (7503144960 : Int) atom0506)) (SparsePolynomial.merge (SparsePolynomial.scale (6954524160 : Int) atom0507) (SparsePolynomial.merge (SparsePolynomial.scale (8592628800 : Int) atom0508) (SparsePolynomial.scale (7029147840 : Int) atom0509)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9631143840 : Int) atom0510) (SparsePolynomial.scale (8158977600 : Int) atom0511)) (SparsePolynomial.merge (SparsePolynomial.scale (8798871360 : Int) atom0512) (SparsePolynomial.merge (SparsePolynomial.scale (10613206080 : Int) atom0513) (SparsePolynomial.scale (4531960320 : Int) atom0514)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7932940800 : Int) atom0515) (SparsePolynomial.scale (9311655360 : Int) atom0516)) (SparsePolynomial.merge (SparsePolynomial.scale (7477765440 : Int) atom0517) (SparsePolynomial.merge (SparsePolynomial.scale (10379483040 : Int) atom0518) (SparsePolynomial.scale (8044739520 : Int) atom0519)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8392186560 : Int) atom0520) (SparsePolynomial.scale (10204830720 : Int) atom0521)) (SparsePolynomial.merge (SparsePolynomial.scale (4927426560 : Int) atom0522) (SparsePolynomial.merge (SparsePolynomial.scale (9870336000 : Int) atom0523) (SparsePolynomial.scale (7722086400 : Int) atom0524))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10978907040 : Int) atom0525) (SparsePolynomial.scale (8678154240 : Int) atom0526)) (SparsePolynomial.merge (SparsePolynomial.scale (7662090240 : Int) atom0527) (SparsePolynomial.merge (SparsePolynomial.scale (11373788160 : Int) atom0528) (SparsePolynomial.scale (6543452160 : Int) atom0529)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10721894400 : Int) atom0530) (SparsePolynomial.scale (15248311200 : Int) atom0531)) (SparsePolynomial.merge (SparsePolynomial.scale (13098516480 : Int) atom0532) (SparsePolynomial.merge (SparsePolynomial.scale (7930137600 : Int) atom0533) (SparsePolynomial.scale (12465129600 : Int) atom0534))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4665765888 : Int) atom0535) (SparsePolynomial.scale (12464877240 : Int) atom0536)) (SparsePolynomial.merge (SparsePolynomial.scale (12188897280 : Int) atom0537) (SparsePolynomial.merge (SparsePolynomial.scale (8198184960 : Int) atom0538) (SparsePolynomial.scale (9925534080 : Int) atom0539)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8286435000 : Int) atom0540) (SparsePolynomial.scale (12894527160 : Int) atom0541)) (SparsePolynomial.merge (SparsePolynomial.scale (8358624720 : Int) atom0542) (SparsePolynomial.merge (SparsePolynomial.scale (10676419920 : Int) atom0543) (SparsePolynomial.scale (4296499200 : Int) atom0544))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5555934720 : Int) atom0545) (SparsePolynomial.scale (8244432000 : Int) atom0546)) (SparsePolynomial.merge (SparsePolynomial.scale (572866560 : Int) atom0547) (SparsePolynomial.merge (SparsePolynomial.scale (3862212480 : Int) atom0548) (SparsePolynomial.scale (2854776960 : Int) atom0549)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (249016320 : Int) atom0550) (SparsePolynomial.scale (633507840 : Int) atom0551)) (SparsePolynomial.merge (SparsePolynomial.scale (519966720 : Int) atom0552) (SparsePolynomial.merge (SparsePolynomial.scale (406425600 : Int) atom0553) (SparsePolynomial.scale (292884480 : Int) atom0554)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (230576640 : Int) atom0555) (SparsePolynomial.scale (108003840 : Int) atom0556)) (SparsePolynomial.merge (SparsePolynomial.scale (10590720 : Int) atom0557) (SparsePolynomial.merge (SparsePolynomial.scale (1501839360 : Int) atom0558) (SparsePolynomial.scale (1167149520 : Int) atom0559)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1344806400 : Int) atom0560) (SparsePolynomial.scale (1764439680 : Int) atom0561)) (SparsePolynomial.merge (SparsePolynomial.scale (766439040 : Int) atom0562) (SparsePolynomial.merge (SparsePolynomial.scale (245414400 : Int) atom0563) (SparsePolynomial.scale (208266240 : Int) atom0564))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (164398080 : Int) atom0565) (SparsePolynomial.scale (170849280 : Int) atom0566)) (SparsePolynomial.merge (SparsePolynomial.scale (264122880 : Int) atom0567) (SparsePolynomial.merge (SparsePolynomial.scale (3555901440 : Int) atom0568) (SparsePolynomial.scale (936962880 : Int) atom0569)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3289076640 : Int) atom0570) (SparsePolynomial.scale (2074914240 : Int) atom0571)) (SparsePolynomial.merge (SparsePolynomial.scale (2798927040 : Int) atom0572) (SparsePolynomial.merge (SparsePolynomial.scale (3522939840 : Int) atom0573) (SparsePolynomial.scale (1300867200 : Int) atom0574)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block007 := by
  rw [block007_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0495_nonneg g hg hA hB) (atom0496_nonneg g hg hA hB)) (add_nonneg (atom0497_nonneg g hg hA hB) (add_nonneg (atom0498_nonneg g hg hA hB) (atom0499_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0500_nonneg g hg hA hB) (atom0501_nonneg g hg hA hB)) (add_nonneg (atom0502_nonneg g hg hA hB) (add_nonneg (atom0503_nonneg g hg hA hB) (atom0504_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0505_nonneg g hg hA hB) (atom0506_nonneg g hg hA hB)) (add_nonneg (atom0507_nonneg g hg hA hB) (add_nonneg (atom0508_nonneg g hg hA hB) (atom0509_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0510_nonneg g hg hA hB) (atom0511_nonneg g hg hA hB)) (add_nonneg (atom0512_nonneg g hg hA hB) (add_nonneg (atom0513_nonneg g hg hA hB) (atom0514_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0515_nonneg g hg hA hB) (atom0516_nonneg g hg hA hB)) (add_nonneg (atom0517_nonneg g hg hA hB) (add_nonneg (atom0518_nonneg g hg hA hB) (atom0519_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0520_nonneg g hg hA hB) (atom0521_nonneg g hg hA hB)) (add_nonneg (atom0522_nonneg g hg hA hB) (add_nonneg (atom0523_nonneg g hg hA hB) (atom0524_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0525_nonneg g hg hA hB) (atom0526_nonneg g hg hA hB)) (add_nonneg (atom0527_nonneg g hg hA hB) (add_nonneg (atom0528_nonneg g hg hA hB) (atom0529_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0530_nonneg g hg hA hB) (atom0531_nonneg g hg hA hB)) (add_nonneg (atom0532_nonneg g hg hA hB) (add_nonneg (atom0533_nonneg g hg hA hB) (atom0534_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0535_nonneg g hg hA hB) (atom0536_nonneg g hg hA hB)) (add_nonneg (atom0537_nonneg g hg hA hB) (add_nonneg (atom0538_nonneg g hg hA hB) (atom0539_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0540_nonneg g hg hA hB) (atom0541_nonneg g hg hA hB)) (add_nonneg (atom0542_nonneg g hg hA hB) (add_nonneg (atom0543_nonneg g hg hA hB) (atom0544_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0545_nonneg g hg hA hB) (atom0546_nonneg g hg hA hB)) (add_nonneg (atom0547_nonneg g hg hA hB) (add_nonneg (atom0548_nonneg g hg hA hB) (atom0549_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0550_nonneg g hg hA hB) (atom0551_nonneg g hg hA hB)) (add_nonneg (atom0552_nonneg g hg hA hB) (add_nonneg (atom0553_nonneg g hg hA hB) (atom0554_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0555_nonneg g hg hA hB) (atom0556_nonneg g hg hA hB)) (add_nonneg (atom0557_nonneg g hg hA hB) (add_nonneg (atom0558_nonneg g hg hA hB) (atom0559_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0560_nonneg g hg hA hB) (atom0561_nonneg g hg hA hB)) (add_nonneg (atom0562_nonneg g hg hA hB) (add_nonneg (atom0563_nonneg g hg hA hB) (atom0564_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0565_nonneg g hg hA hB) (atom0566_nonneg g hg hA hB)) (add_nonneg (atom0567_nonneg g hg hA hB) (add_nonneg (atom0568_nonneg g hg hA hB) (atom0569_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0570_nonneg g hg hA hB) (atom0571_nonneg g hg hA hB)) (add_nonneg (atom0572_nonneg g hg hA hB) (add_nonneg (atom0573_nonneg g hg hA hB) (atom0574_nonneg g hg hA hB))))))))

end APPT.Finite18
