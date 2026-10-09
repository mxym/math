import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0576 : SparsePolynomial.Poly := [([2,2,7], 1)]
theorem eval_atom0576 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0576 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0576_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13552237298304 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0577 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0577 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0577_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13277370355200 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578 : SparsePolynomial.Poly := [([2,2,9], 1)]
theorem eval_atom0578 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0578 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0578_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12927508070400 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579 : SparsePolynomial.Poly := [([2,2,10], 1)]
theorem eval_atom0579 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0579 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0579_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12577645785600 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580 : SparsePolynomial.Poly := [([2,2,11], 1)]
theorem eval_atom0580 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0580 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0580_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11915859916800 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581 : SparsePolynomial.Poly := [([2,2,12], 1)]
theorem eval_atom0581 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0581 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0581_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9204520908800 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582 : SparsePolynomial.Poly := [([2,2,13], 1)]
theorem eval_atom0582 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0582 = ((g 2) * (g 2) * (g 13)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0582_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8236260748800 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583 : SparsePolynomial.Poly := [([2,2,14], 1)]
theorem eval_atom0583 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0583 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0583_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8145412531200 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584 : SparsePolynomial.Poly := [([2,2,15], 1)]
theorem eval_atom0584 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0584 = ((g 2) * (g 2) * (g 15)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0584_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12461669337600 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585 : SparsePolynomial.Poly := [([2,2,16], 1)]
theorem eval_atom0585 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0585 = ((g 2) * (g 2) * (g 16)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0585_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3160358208000 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586 : SparsePolynomial.Poly := [([2,2,17], 1)]
theorem eval_atom0586 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0586 = ((g 2) * (g 2) * (g 17)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0586_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9873255974400 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587 : SparsePolynomial.Poly := [([2,2,18], 1)]
theorem eval_atom0587 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0587 = ((g 2) * (g 2) * (g 18)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0587_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1606273804800 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588 : SparsePolynomial.Poly := [([2,2,20], 1)]
theorem eval_atom0588 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0588 = ((g 2) * (g 2) * (g 20)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0588_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3063711168000 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0589 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0589 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0589_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11203324876800 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0590 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0590 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0590_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21357062899200 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0591 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0591 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0591_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23290231970304 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0592 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0592 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0592_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23147295091200 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0593 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0593 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0593_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25005300887808 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0594 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0594 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0594_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24960064550400 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595 : SparsePolynomial.Poly := [([2,3,9], 1)]
theorem eval_atom0595 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0595 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0595_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24764837529600 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596 : SparsePolynomial.Poly := [([2,3,10], 1)]
theorem eval_atom0596 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0596 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0596_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24569610508800 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597 : SparsePolynomial.Poly := [([2,3,11], 1)]
theorem eval_atom0597 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0597 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0597_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23750536320000 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598 : SparsePolynomial.Poly := [([2,3,12], 1)]
theorem eval_atom0598 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0598 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0598_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18832355852800 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599 : SparsePolynomial.Poly := [([2,3,13], 1)]
theorem eval_atom0599 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0599 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0599_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17400333081600 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600 : SparsePolynomial.Poly := [([2,3,14], 1)]
theorem eval_atom0600 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0600 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0600_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17723134195200 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601 : SparsePolynomial.Poly := [([2,3,15], 1)]
theorem eval_atom0601 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0601 = ((g 2) * (g 3) * (g 15)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0601_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26860145356800 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602 : SparsePolynomial.Poly := [([2,3,16], 1)]
theorem eval_atom0602 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0602 = ((g 2) * (g 3) * (g 16)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0602_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11444942476800 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603 : SparsePolynomial.Poly := [([2,3,17], 1)]
theorem eval_atom0603 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0603 = ((g 2) * (g 3) * (g 17)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0603_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22692313728000 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604 : SparsePolynomial.Poly := [([2,3,18], 1)]
theorem eval_atom0604 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0604 = ((g 2) * (g 3) * (g 18)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0604_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10745217907200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605 : SparsePolynomial.Poly := [([2,3,19], 1)]
theorem eval_atom0605 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0605 = ((g 2) * (g 3) * (g 19)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0605_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9566124019200 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606 : SparsePolynomial.Poly := [([2,3,20], 1)]
theorem eval_atom0606 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0606 = ((g 2) * (g 3) * (g 20)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0606_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13057015104000 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0607 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0607 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0607_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11020661971200 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0608 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0608 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0608_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20212761945600 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0609 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0609 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0609_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20543623833600 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0610 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0610 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0610_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22906127179008 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0611 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0611 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0611_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23365388390400 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612 : SparsePolynomial.Poly := [([2,4,9], 1)]
theorem eval_atom0612 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0612 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0612_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23674658918400 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613 : SparsePolynomial.Poly := [([2,4,10], 1)]
theorem eval_atom0613 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0613 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0613_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23983929446400 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614 : SparsePolynomial.Poly := [([2,4,11], 1)]
theorem eval_atom0614 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0614 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0614_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23669352806400 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615 : SparsePolynomial.Poly := [([2,4,12], 1)]
theorem eval_atom0615 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0615 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0615_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20066681734400 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616 : SparsePolynomial.Poly := [([2,4,13], 1)]
theorem eval_atom0616 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0616 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0616_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19784615558400 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617 : SparsePolynomial.Poly := [([2,4,14], 1)]
theorem eval_atom0617 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0617 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0617_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20379961324800 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618 : SparsePolynomial.Poly := [([2,4,15], 1)]
theorem eval_atom0618 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0618 = ((g 2) * (g 4) * (g 15)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0618_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28796952038400 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619 : SparsePolynomial.Poly := [([2,4,16], 1)]
theorem eval_atom0619 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0619 = ((g 2) * (g 4) * (g 16)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0619_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17572968856800 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620 : SparsePolynomial.Poly := [([2,4,17], 1)]
theorem eval_atom0620 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0620 = ((g 2) * (g 4) * (g 17)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0620_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25638115507200 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621 : SparsePolynomial.Poly := [([2,4,18], 1)]
theorem eval_atom0621 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0621 = ((g 2) * (g 4) * (g 18)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0621_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19002620196000 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622 : SparsePolynomial.Poly := [([2,4,19], 1)]
theorem eval_atom0622 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0622 = ((g 2) * (g 4) * (g 19)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0622_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19156772224800 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623 : SparsePolynomial.Poly := [([2,4,20], 1)]
theorem eval_atom0623 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0623 = ((g 2) * (g 4) * (g 20)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0623_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23980909226400 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0624 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0624 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0624_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14748338304000 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0625 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0625 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0625_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27897168096000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0626 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0626 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0626_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24726406984704 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0627 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0627 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0627_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24753468155904 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628 : SparsePolynomial.Poly := [([2,5,9], 1)]
theorem eval_atom0628 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0628 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0628_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26296921384704 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629 : SparsePolynomial.Poly := [([2,5,10], 1)]
theorem eval_atom0629 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0629 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0629_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26381004309504 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630 : SparsePolynomial.Poly := [([2,5,11], 1)]
theorem eval_atom0630 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0630 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0630_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26570925218304 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631 : SparsePolynomial.Poly := [([2,5,12], 1)]
theorem eval_atom0631 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0631 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0631_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24050700994304 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632 : SparsePolynomial.Poly := [([2,5,13], 1)]
theorem eval_atom0632 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0632 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0632_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23597569557504 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633 : SparsePolynomial.Poly := [([2,5,14], 1)]
theorem eval_atom0633 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0633 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0633_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24283763541504 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634 : SparsePolynomial.Poly := [([2,5,15], 1)]
theorem eval_atom0634 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0634 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0634_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33716514645504 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635 : SparsePolynomial.Poly := [([2,5,16], 1)]
theorem eval_atom0635 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0635 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0635_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22622798557440 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636 : SparsePolynomial.Poly := [([2,5,17], 1)]
theorem eval_atom0636 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0636 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0636_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31566673211904 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637 : SparsePolynomial.Poly := [([2,5,18], 1)]
theorem eval_atom0637 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0637 = ((g 2) * (g 5) * (g 18)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0637_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26162808429312 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638 : SparsePolynomial.Poly := [([2,5,19], 1)]
theorem eval_atom0638 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0638 = ((g 2) * (g 5) * (g 19)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0638_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27693583407360 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639 : SparsePolynomial.Poly := [([2,5,20], 1)]
theorem eval_atom0639 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0639 = ((g 2) * (g 5) * (g 20)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0639_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33894343358208 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0640 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0640 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0640_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18705068121600 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0641 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0641 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0641_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34252905717504 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0642 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0642 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0642_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30315115958400 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0643 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0643 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0643_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27620120102400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0644 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0644 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0644_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27885899462400 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0645 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0645 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0645_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27580741171200 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646 : SparsePolynomial.Poly := [([2,6,12], 1)]
theorem eval_atom0646 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0646 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0646_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25569126732800 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647 : SparsePolynomial.Poly := [([2,6,13], 1)]
theorem eval_atom0647 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0647 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0647_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25300591142400 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648 : SparsePolynomial.Poly := [([2,6,14], 1)]
theorem eval_atom0648 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0648 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0648_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25909467494400 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649 : SparsePolynomial.Poly := [([2,6,15], 1)]
theorem eval_atom0649 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0649 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0649_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36559971302400 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650 : SparsePolynomial.Poly := [([2,6,16], 1)]
theorem eval_atom0650 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0650 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0650_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25733446502400 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651 : SparsePolynomial.Poly := [([2,6,17], 1)]
theorem eval_atom0651 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0651 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0651_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35419124966400 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652 : SparsePolynomial.Poly := [([2,6,18], 1)]
theorem eval_atom0652 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0652 = ((g 2) * (g 6) * (g 18)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0652_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32397979622400 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653 : SparsePolynomial.Poly := [([2,6,19], 1)]
theorem eval_atom0653 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0653 = ((g 2) * (g 6) * (g 19)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0653_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36037542643200 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654 : SparsePolynomial.Poly := [([2,6,20], 1)]
theorem eval_atom0654 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0654 = ((g 2) * (g 6) * (g 20)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0654_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44347090636800 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0655 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom0655 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0655_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20414982530304 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block009 : SparsePolynomial.Poly := [([2,2,7], 13552237298304), ([2,2,8], 13277370355200), ([2,2,9], 12927508070400), ([2,2,10], 12577645785600), ([2,2,11], 11915859916800), ([2,2,12], 9204520908800), ([2,2,13], 8236260748800), ([2,2,14], 8145412531200), ([2,2,15], 12461669337600), ([2,2,16], 3160358208000), ([2,2,17], 9873255974400), ([2,2,18], 1606273804800), ([2,2,20], 3063711168000), ([2,3,3], 11203324876800), ([2,3,4], 21357062899200), ([2,3,5], 23290231970304), ([2,3,6], 23147295091200), ([2,3,7], 25005300887808), ([2,3,8], 24960064550400), ([2,3,9], 24764837529600), ([2,3,10], 24569610508800), ([2,3,11], 23750536320000), ([2,3,12], 18832355852800), ([2,3,13], 17400333081600), ([2,3,14], 17723134195200), ([2,3,15], 26860145356800), ([2,3,16], 11444942476800), ([2,3,17], 22692313728000), ([2,3,18], 10745217907200), ([2,3,19], 9566124019200), ([2,3,20], 13057015104000), ([2,4,4], 11020661971200), ([2,4,5], 20212761945600), ([2,4,6], 20543623833600), ([2,4,7], 22906127179008), ([2,4,8], 23365388390400), ([2,4,9], 23674658918400), ([2,4,10], 23983929446400), ([2,4,11], 23669352806400), ([2,4,12], 20066681734400), ([2,4,13], 19784615558400), ([2,4,14], 20379961324800), ([2,4,15], 28796952038400), ([2,4,16], 17572968856800), ([2,4,17], 25638115507200), ([2,4,18], 19002620196000), ([2,4,19], 19156772224800), ([2,4,20], 23980909226400), ([2,5,5], 14748338304000), ([2,5,6], 27897168096000), ([2,5,7], 24726406984704), ([2,5,8], 24753468155904), ([2,5,9], 26296921384704), ([2,5,10], 26381004309504), ([2,5,11], 26570925218304), ([2,5,12], 24050700994304), ([2,5,13], 23597569557504), ([2,5,14], 24283763541504), ([2,5,15], 33716514645504), ([2,5,16], 22622798557440), ([2,5,17], 31566673211904), ([2,5,18], 26162808429312), ([2,5,19], 27693583407360), ([2,5,20], 33894343358208), ([2,6,6], 18705068121600), ([2,6,7], 34252905717504), ([2,6,8], 30315115958400), ([2,6,9], 27620120102400), ([2,6,10], 27885899462400), ([2,6,11], 27580741171200), ([2,6,12], 25569126732800), ([2,6,13], 25300591142400), ([2,6,14], 25909467494400), ([2,6,15], 36559971302400), ([2,6,16], 25733446502400), ([2,6,17], 35419124966400), ([2,6,18], 32397979622400), ([2,6,19], 36037542643200), ([2,6,20], 44347090636800), ([2,7,7], 20414982530304)]
theorem block009_data : block009 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13552237298304 : Int) atom0576) (SparsePolynomial.scale (13277370355200 : Int) atom0577)) (SparsePolynomial.merge (SparsePolynomial.scale (12927508070400 : Int) atom0578) (SparsePolynomial.merge (SparsePolynomial.scale (12577645785600 : Int) atom0579) (SparsePolynomial.scale (11915859916800 : Int) atom0580)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9204520908800 : Int) atom0581) (SparsePolynomial.scale (8236260748800 : Int) atom0582)) (SparsePolynomial.merge (SparsePolynomial.scale (8145412531200 : Int) atom0583) (SparsePolynomial.merge (SparsePolynomial.scale (12461669337600 : Int) atom0584) (SparsePolynomial.scale (3160358208000 : Int) atom0585))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9873255974400 : Int) atom0586) (SparsePolynomial.scale (1606273804800 : Int) atom0587)) (SparsePolynomial.merge (SparsePolynomial.scale (3063711168000 : Int) atom0588) (SparsePolynomial.merge (SparsePolynomial.scale (11203324876800 : Int) atom0589) (SparsePolynomial.scale (21357062899200 : Int) atom0590)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23290231970304 : Int) atom0591) (SparsePolynomial.scale (23147295091200 : Int) atom0592)) (SparsePolynomial.merge (SparsePolynomial.scale (25005300887808 : Int) atom0593) (SparsePolynomial.merge (SparsePolynomial.scale (24960064550400 : Int) atom0594) (SparsePolynomial.scale (24764837529600 : Int) atom0595)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24569610508800 : Int) atom0596) (SparsePolynomial.scale (23750536320000 : Int) atom0597)) (SparsePolynomial.merge (SparsePolynomial.scale (18832355852800 : Int) atom0598) (SparsePolynomial.merge (SparsePolynomial.scale (17400333081600 : Int) atom0599) (SparsePolynomial.scale (17723134195200 : Int) atom0600)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26860145356800 : Int) atom0601) (SparsePolynomial.scale (11444942476800 : Int) atom0602)) (SparsePolynomial.merge (SparsePolynomial.scale (22692313728000 : Int) atom0603) (SparsePolynomial.merge (SparsePolynomial.scale (10745217907200 : Int) atom0604) (SparsePolynomial.scale (9566124019200 : Int) atom0605))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13057015104000 : Int) atom0606) (SparsePolynomial.scale (11020661971200 : Int) atom0607)) (SparsePolynomial.merge (SparsePolynomial.scale (20212761945600 : Int) atom0608) (SparsePolynomial.merge (SparsePolynomial.scale (20543623833600 : Int) atom0609) (SparsePolynomial.scale (22906127179008 : Int) atom0610)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23365388390400 : Int) atom0611) (SparsePolynomial.scale (23674658918400 : Int) atom0612)) (SparsePolynomial.merge (SparsePolynomial.scale (23983929446400 : Int) atom0613) (SparsePolynomial.merge (SparsePolynomial.scale (23669352806400 : Int) atom0614) (SparsePolynomial.scale (20066681734400 : Int) atom0615))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19784615558400 : Int) atom0616) (SparsePolynomial.scale (20379961324800 : Int) atom0617)) (SparsePolynomial.merge (SparsePolynomial.scale (28796952038400 : Int) atom0618) (SparsePolynomial.merge (SparsePolynomial.scale (17572968856800 : Int) atom0619) (SparsePolynomial.scale (25638115507200 : Int) atom0620)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19002620196000 : Int) atom0621) (SparsePolynomial.scale (19156772224800 : Int) atom0622)) (SparsePolynomial.merge (SparsePolynomial.scale (23980909226400 : Int) atom0623) (SparsePolynomial.merge (SparsePolynomial.scale (14748338304000 : Int) atom0624) (SparsePolynomial.scale (27897168096000 : Int) atom0625))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24726406984704 : Int) atom0626) (SparsePolynomial.scale (24753468155904 : Int) atom0627)) (SparsePolynomial.merge (SparsePolynomial.scale (26296921384704 : Int) atom0628) (SparsePolynomial.merge (SparsePolynomial.scale (26381004309504 : Int) atom0629) (SparsePolynomial.scale (26570925218304 : Int) atom0630)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24050700994304 : Int) atom0631) (SparsePolynomial.scale (23597569557504 : Int) atom0632)) (SparsePolynomial.merge (SparsePolynomial.scale (24283763541504 : Int) atom0633) (SparsePolynomial.merge (SparsePolynomial.scale (33716514645504 : Int) atom0634) (SparsePolynomial.scale (22622798557440 : Int) atom0635)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31566673211904 : Int) atom0636) (SparsePolynomial.scale (26162808429312 : Int) atom0637)) (SparsePolynomial.merge (SparsePolynomial.scale (27693583407360 : Int) atom0638) (SparsePolynomial.merge (SparsePolynomial.scale (33894343358208 : Int) atom0639) (SparsePolynomial.scale (18705068121600 : Int) atom0640)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34252905717504 : Int) atom0641) (SparsePolynomial.scale (30315115958400 : Int) atom0642)) (SparsePolynomial.merge (SparsePolynomial.scale (27620120102400 : Int) atom0643) (SparsePolynomial.merge (SparsePolynomial.scale (27885899462400 : Int) atom0644) (SparsePolynomial.scale (27580741171200 : Int) atom0645))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25569126732800 : Int) atom0646) (SparsePolynomial.scale (25300591142400 : Int) atom0647)) (SparsePolynomial.merge (SparsePolynomial.scale (25909467494400 : Int) atom0648) (SparsePolynomial.merge (SparsePolynomial.scale (36559971302400 : Int) atom0649) (SparsePolynomial.scale (25733446502400 : Int) atom0650)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35419124966400 : Int) atom0651) (SparsePolynomial.scale (32397979622400 : Int) atom0652)) (SparsePolynomial.merge (SparsePolynomial.scale (36037542643200 : Int) atom0653) (SparsePolynomial.merge (SparsePolynomial.scale (44347090636800 : Int) atom0654) (SparsePolynomial.scale (20414982530304 : Int) atom0655)))))))) := by decide +kernel
theorem block009_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block009 := by
  rw [block009_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0576_nonneg g hg hA hB) (atom0577_nonneg g hg hA hB)) (add_nonneg (atom0578_nonneg g hg hA hB) (add_nonneg (atom0579_nonneg g hg hA hB) (atom0580_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0581_nonneg g hg hA hB) (atom0582_nonneg g hg hA hB)) (add_nonneg (atom0583_nonneg g hg hA hB) (add_nonneg (atom0584_nonneg g hg hA hB) (atom0585_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0586_nonneg g hg hA hB) (atom0587_nonneg g hg hA hB)) (add_nonneg (atom0588_nonneg g hg hA hB) (add_nonneg (atom0589_nonneg g hg hA hB) (atom0590_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0591_nonneg g hg hA hB) (atom0592_nonneg g hg hA hB)) (add_nonneg (atom0593_nonneg g hg hA hB) (add_nonneg (atom0594_nonneg g hg hA hB) (atom0595_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0596_nonneg g hg hA hB) (atom0597_nonneg g hg hA hB)) (add_nonneg (atom0598_nonneg g hg hA hB) (add_nonneg (atom0599_nonneg g hg hA hB) (atom0600_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0601_nonneg g hg hA hB) (atom0602_nonneg g hg hA hB)) (add_nonneg (atom0603_nonneg g hg hA hB) (add_nonneg (atom0604_nonneg g hg hA hB) (atom0605_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0606_nonneg g hg hA hB) (atom0607_nonneg g hg hA hB)) (add_nonneg (atom0608_nonneg g hg hA hB) (add_nonneg (atom0609_nonneg g hg hA hB) (atom0610_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0611_nonneg g hg hA hB) (atom0612_nonneg g hg hA hB)) (add_nonneg (atom0613_nonneg g hg hA hB) (add_nonneg (atom0614_nonneg g hg hA hB) (atom0615_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0616_nonneg g hg hA hB) (atom0617_nonneg g hg hA hB)) (add_nonneg (atom0618_nonneg g hg hA hB) (add_nonneg (atom0619_nonneg g hg hA hB) (atom0620_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0621_nonneg g hg hA hB) (atom0622_nonneg g hg hA hB)) (add_nonneg (atom0623_nonneg g hg hA hB) (add_nonneg (atom0624_nonneg g hg hA hB) (atom0625_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0626_nonneg g hg hA hB) (atom0627_nonneg g hg hA hB)) (add_nonneg (atom0628_nonneg g hg hA hB) (add_nonneg (atom0629_nonneg g hg hA hB) (atom0630_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0631_nonneg g hg hA hB) (atom0632_nonneg g hg hA hB)) (add_nonneg (atom0633_nonneg g hg hA hB) (add_nonneg (atom0634_nonneg g hg hA hB) (atom0635_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0636_nonneg g hg hA hB) (atom0637_nonneg g hg hA hB)) (add_nonneg (atom0638_nonneg g hg hA hB) (add_nonneg (atom0639_nonneg g hg hA hB) (atom0640_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0641_nonneg g hg hA hB) (atom0642_nonneg g hg hA hB)) (add_nonneg (atom0643_nonneg g hg hA hB) (add_nonneg (atom0644_nonneg g hg hA hB) (atom0645_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0646_nonneg g hg hA hB) (atom0647_nonneg g hg hA hB)) (add_nonneg (atom0648_nonneg g hg hA hB) (add_nonneg (atom0649_nonneg g hg hA hB) (atom0650_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0651_nonneg g hg hA hB) (atom0652_nonneg g hg hA hB)) (add_nonneg (atom0653_nonneg g hg hA hB) (add_nonneg (atom0654_nonneg g hg hA hB) (atom0655_nonneg g hg hA hB))))))))

end APPT.Finite21
