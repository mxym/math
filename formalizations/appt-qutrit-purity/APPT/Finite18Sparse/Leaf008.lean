import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0575 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0575 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0575 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0575_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1710823680 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0576 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0576 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0576_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1050595200 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0577 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0577 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0577_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1120536960 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom0578 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0578 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0578_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1076668800 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom0579 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0579 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0579_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1136664960 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom0580 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0580 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0580_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1283483520 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581 : SparsePolynomial.Poly := [([3,5,12], 1)]
theorem eval_atom0581 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0581 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0581_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4108124160 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582 : SparsePolynomial.Poly := [([3,5,13], 1)]
theorem eval_atom0582 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0582 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0582_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2212409520 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583 : SparsePolynomial.Poly := [([3,5,14], 1)]
theorem eval_atom0583 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0583 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0583_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4243854240 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584 : SparsePolynomial.Poly := [([3,5,15], 1)]
theorem eval_atom0584 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0584 = ((g 3) * (g 5) * (g 15)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0584_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3755442960 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585 : SparsePolynomial.Poly := [([3,5,16], 1)]
theorem eval_atom0585 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0585 = ((g 3) * (g 5) * (g 16)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0585_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4731662160 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586 : SparsePolynomial.Poly := [([3,5,17], 1)]
theorem eval_atom0586 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0586 = ((g 3) * (g 5) * (g 17)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0586_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5707881360 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0587 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0587 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0587_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1291190400 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0588 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0588 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0588_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2136332160 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0589 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0589 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0589_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2155954560 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590 : SparsePolynomial.Poly := [([3,6,9], 1)]
theorem eval_atom0590 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0590 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0590_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2168856960 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591 : SparsePolynomial.Poly := [([3,6,10], 1)]
theorem eval_atom0591 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0591 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0591_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2232078720 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592 : SparsePolynomial.Poly := [([3,6,11], 1)]
theorem eval_atom0592 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0592 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0592_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2382122880 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593 : SparsePolynomial.Poly := [([3,6,12], 1)]
theorem eval_atom0593 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0593 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0593_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4660346880 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594 : SparsePolynomial.Poly := [([3,6,13], 1)]
theorem eval_atom0594 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0594 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0594_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3403865520 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595 : SparsePolynomial.Poly := [([3,6,14], 1)]
theorem eval_atom0595 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0595 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0595_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5198631840 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596 : SparsePolynomial.Poly := [([3,6,15], 1)]
theorem eval_atom0596 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0596 = ((g 3) * (g 6) * (g 15)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0596_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5126081040 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597 : SparsePolynomial.Poly := [([3,6,16], 1)]
theorem eval_atom0597 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0597 = ((g 3) * (g 6) * (g 16)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0597_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6220679760 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598 : SparsePolynomial.Poly := [([3,6,17], 1)]
theorem eval_atom0598 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0598 = ((g 3) * (g 6) * (g 17)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0598_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7315278480 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0599 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0599 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0599_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1726375680 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0600 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0600 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0600_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3118099200 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601 : SparsePolynomial.Poly := [([3,7,9], 1)]
theorem eval_atom0601 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0601 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0601_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3030362880 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602 : SparsePolynomial.Poly := [([3,7,10], 1)]
theorem eval_atom0602 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0602 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0602_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3046490880 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603 : SparsePolynomial.Poly := [([3,7,11], 1)]
theorem eval_atom0603 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0603 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0603_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3149441280 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604 : SparsePolynomial.Poly := [([3,7,12], 1)]
theorem eval_atom0604 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0604 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0604_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5212569600 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605 : SparsePolynomial.Poly := [([3,7,13], 1)]
theorem eval_atom0605 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0605 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0605_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4254706080 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606 : SparsePolynomial.Poly := [([3,7,14], 1)]
theorem eval_atom0606 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0606 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0606_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6153409440 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607 : SparsePolynomial.Poly := [([3,7,15], 1)]
theorem eval_atom0607 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0607 = ((g 3) * (g 7) * (g 15)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0607_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6238153440 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608 : SparsePolynomial.Poly := [([3,7,16], 1)]
theorem eval_atom0608 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0608 = ((g 3) * (g 7) * (g 16)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0608_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7522604640 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609 : SparsePolynomial.Poly := [([3,7,17], 1)]
theorem eval_atom0609 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0609 = ((g 3) * (g 7) * (g 17)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0609_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8807055840 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0610 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0610 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0610_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2272957440 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611 : SparsePolynomial.Poly := [([3,8,9], 1)]
theorem eval_atom0611 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0611 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0611_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4097118720 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612 : SparsePolynomial.Poly := [([3,8,10], 1)]
theorem eval_atom0612 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0612 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0612_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4015833600 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613 : SparsePolynomial.Poly := [([3,8,11], 1)]
theorem eval_atom0613 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0613 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0613_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4021370880 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614 : SparsePolynomial.Poly := [([3,8,12], 1)]
theorem eval_atom0614 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0614 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0614_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5867258880 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615 : SparsePolynomial.Poly := [([3,8,13], 1)]
theorem eval_atom0615 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0615 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0615_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5037388800 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616 : SparsePolynomial.Poly := [([3,8,14], 1)]
theorem eval_atom0616 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0616 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0616_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7210653600 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617 : SparsePolynomial.Poly := [([3,8,15], 1)]
theorem eval_atom0617 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0617 = ((g 3) * (g 8) * (g 15)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0617_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7037168640 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618 : SparsePolynomial.Poly := [([3,8,16], 1)]
theorem eval_atom0618 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0618 = ((g 3) * (g 8) * (g 16)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0618_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8364979200 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619 : SparsePolynomial.Poly := [([3,8,17], 1)]
theorem eval_atom0619 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0619 = ((g 3) * (g 8) * (g 17)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0619_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9692789760 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom0620 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0620 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0620_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2809259520 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621 : SparsePolynomial.Poly := [([3,9,10], 1)]
theorem eval_atom0621 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0621 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0621_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5038786560 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622 : SparsePolynomial.Poly := [([3,9,11], 1)]
theorem eval_atom0622 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0622 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0622_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4896591360 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623 : SparsePolynomial.Poly := [([3,9,12], 1)]
theorem eval_atom0623 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0623 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0623_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6618561600 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624 : SparsePolynomial.Poly := [([3,9,13], 1)]
theorem eval_atom0624 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0624 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0624_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5688588480 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625 : SparsePolynomial.Poly := [([3,9,14], 1)]
theorem eval_atom0625 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0625 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0625_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8147367840 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626 : SparsePolynomial.Poly := [([3,9,15], 1)]
theorem eval_atom0626 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0626 = ((g 3) * (g 9) * (g 15)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0626_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7535791680 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627 : SparsePolynomial.Poly := [([3,9,16], 1)]
theorem eval_atom0627 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0627 = ((g 3) * (g 9) * (g 16)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0627_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8811128640 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628 : SparsePolynomial.Poly := [([3,9,17], 1)]
theorem eval_atom0628 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0628 = ((g 3) * (g 9) * (g 17)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0628_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10086465600 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom0629 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0629 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0629_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3318489600 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630 : SparsePolynomial.Poly := [([3,10,11], 1)]
theorem eval_atom0630 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0630 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0630_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5962744320 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631 : SparsePolynomial.Poly := [([3,10,12], 1)]
theorem eval_atom0631 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0631 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0631_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7475643840 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632 : SparsePolynomial.Poly := [([3,10,13], 1)]
theorem eval_atom0632 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0632 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0632_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6325581120 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633 : SparsePolynomial.Poly := [([3,10,14], 1)]
theorem eval_atom0633 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0633 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0633_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9134401440 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634 : SparsePolynomial.Poly := [([3,10,15], 1)]
theorem eval_atom0634 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0634 = ((g 3) * (g 10) * (g 15)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0634_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7710567360 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635 : SparsePolynomial.Poly := [([3,10,16], 1)]
theorem eval_atom0635 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0635 = ((g 3) * (g 10) * (g 16)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0635_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8743776960 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636 : SparsePolynomial.Poly := [([3,10,17], 1)]
theorem eval_atom0636 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0636 = ((g 3) * (g 10) * (g 17)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0636_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10067742720 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom0637 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0637 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0637_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4066836480 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638 : SparsePolynomial.Poly := [([3,11,12], 1)]
theorem eval_atom0638 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0638 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0638_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8253020160 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639 : SparsePolynomial.Poly := [([3,11,13], 1)]
theorem eval_atom0639 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0639 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0639_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6758277120 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640 : SparsePolynomial.Poly := [([3,11,14], 1)]
theorem eval_atom0640 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0640 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0640_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9891879840 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641 : SparsePolynomial.Poly := [([3,11,15], 1)]
theorem eval_atom0641 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0641 = ((g 3) * (g 11) * (g 15)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0641_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8512035840 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642 : SparsePolynomial.Poly := [([3,11,16], 1)]
theorem eval_atom0642 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0642 = ((g 3) * (g 11) * (g 16)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0642_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8191733760 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643 : SparsePolynomial.Poly := [([3,11,17], 1)]
theorem eval_atom0643 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0643 = ((g 3) * (g 11) * (g 17)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0643_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11444912640 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644 : SparsePolynomial.Poly := [([3,12,12], 1)]
theorem eval_atom0644 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0644 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0644_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5763502080 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645 : SparsePolynomial.Poly := [([3,12,13], 1)]
theorem eval_atom0645 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0645 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0645_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9752279040 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646 : SparsePolynomial.Poly := [([3,12,14], 1)]
theorem eval_atom0646 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0646 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0646_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14480618400 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647 : SparsePolynomial.Poly := [([3,12,15], 1)]
theorem eval_atom0647 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0647 = ((g 3) * (g 12) * (g 15)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0647_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13034649600 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648 : SparsePolynomial.Poly := [([3,12,16], 1)]
theorem eval_atom0648 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0648 = ((g 3) * (g 12) * (g 16)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0648_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8457523200 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649 : SparsePolynomial.Poly := [([3,12,17], 1)]
theorem eval_atom0649 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0649 = ((g 3) * (g 12) * (g 17)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0649_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12763699200 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650 : SparsePolynomial.Poly := [([3,13,13], 1)]
theorem eval_atom0650 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0650 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0650_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4178055168 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651 : SparsePolynomial.Poly := [([3,13,14], 1)]
theorem eval_atom0651 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0651 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0651_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11741697720 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652 : SparsePolynomial.Poly := [([3,13,15], 1)]
theorem eval_atom0652 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0652 = ((g 3) * (g 13) * (g 15)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0652_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11815050240 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653 : SparsePolynomial.Poly := [([3,13,16], 1)]
theorem eval_atom0653 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0653 = ((g 3) * (g 13) * (g 16)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0653_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8173670400 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654 : SparsePolynomial.Poly := [([3,13,17], 1)]
theorem eval_atom0654 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0654 = ((g 3) * (g 13) * (g 17)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0654_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9910817280 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block008 : SparsePolynomial.Poly := [([3,5,6], 1710823680), ([3,5,7], 1050595200), ([3,5,8], 1120536960), ([3,5,9], 1076668800), ([3,5,10], 1136664960), ([3,5,11], 1283483520), ([3,5,12], 4108124160), ([3,5,13], 2212409520), ([3,5,14], 4243854240), ([3,5,15], 3755442960), ([3,5,16], 4731662160), ([3,5,17], 5707881360), ([3,6,6], 1291190400), ([3,6,7], 2136332160), ([3,6,8], 2155954560), ([3,6,9], 2168856960), ([3,6,10], 2232078720), ([3,6,11], 2382122880), ([3,6,12], 4660346880), ([3,6,13], 3403865520), ([3,6,14], 5198631840), ([3,6,15], 5126081040), ([3,6,16], 6220679760), ([3,6,17], 7315278480), ([3,7,7], 1726375680), ([3,7,8], 3118099200), ([3,7,9], 3030362880), ([3,7,10], 3046490880), ([3,7,11], 3149441280), ([3,7,12], 5212569600), ([3,7,13], 4254706080), ([3,7,14], 6153409440), ([3,7,15], 6238153440), ([3,7,16], 7522604640), ([3,7,17], 8807055840), ([3,8,8], 2272957440), ([3,8,9], 4097118720), ([3,8,10], 4015833600), ([3,8,11], 4021370880), ([3,8,12], 5867258880), ([3,8,13], 5037388800), ([3,8,14], 7210653600), ([3,8,15], 7037168640), ([3,8,16], 8364979200), ([3,8,17], 9692789760), ([3,9,9], 2809259520), ([3,9,10], 5038786560), ([3,9,11], 4896591360), ([3,9,12], 6618561600), ([3,9,13], 5688588480), ([3,9,14], 8147367840), ([3,9,15], 7535791680), ([3,9,16], 8811128640), ([3,9,17], 10086465600), ([3,10,10], 3318489600), ([3,10,11], 5962744320), ([3,10,12], 7475643840), ([3,10,13], 6325581120), ([3,10,14], 9134401440), ([3,10,15], 7710567360), ([3,10,16], 8743776960), ([3,10,17], 10067742720), ([3,11,11], 4066836480), ([3,11,12], 8253020160), ([3,11,13], 6758277120), ([3,11,14], 9891879840), ([3,11,15], 8512035840), ([3,11,16], 8191733760), ([3,11,17], 11444912640), ([3,12,12], 5763502080), ([3,12,13], 9752279040), ([3,12,14], 14480618400), ([3,12,15], 13034649600), ([3,12,16], 8457523200), ([3,12,17], 12763699200), ([3,13,13], 4178055168), ([3,13,14], 11741697720), ([3,13,15], 11815050240), ([3,13,16], 8173670400), ([3,13,17], 9910817280)]
theorem block008_data : block008 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1710823680 : Int) atom0575) (SparsePolynomial.scale (1050595200 : Int) atom0576)) (SparsePolynomial.merge (SparsePolynomial.scale (1120536960 : Int) atom0577) (SparsePolynomial.merge (SparsePolynomial.scale (1076668800 : Int) atom0578) (SparsePolynomial.scale (1136664960 : Int) atom0579)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1283483520 : Int) atom0580) (SparsePolynomial.scale (4108124160 : Int) atom0581)) (SparsePolynomial.merge (SparsePolynomial.scale (2212409520 : Int) atom0582) (SparsePolynomial.merge (SparsePolynomial.scale (4243854240 : Int) atom0583) (SparsePolynomial.scale (3755442960 : Int) atom0584))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4731662160 : Int) atom0585) (SparsePolynomial.scale (5707881360 : Int) atom0586)) (SparsePolynomial.merge (SparsePolynomial.scale (1291190400 : Int) atom0587) (SparsePolynomial.merge (SparsePolynomial.scale (2136332160 : Int) atom0588) (SparsePolynomial.scale (2155954560 : Int) atom0589)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2168856960 : Int) atom0590) (SparsePolynomial.scale (2232078720 : Int) atom0591)) (SparsePolynomial.merge (SparsePolynomial.scale (2382122880 : Int) atom0592) (SparsePolynomial.merge (SparsePolynomial.scale (4660346880 : Int) atom0593) (SparsePolynomial.scale (3403865520 : Int) atom0594)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5198631840 : Int) atom0595) (SparsePolynomial.scale (5126081040 : Int) atom0596)) (SparsePolynomial.merge (SparsePolynomial.scale (6220679760 : Int) atom0597) (SparsePolynomial.merge (SparsePolynomial.scale (7315278480 : Int) atom0598) (SparsePolynomial.scale (1726375680 : Int) atom0599)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3118099200 : Int) atom0600) (SparsePolynomial.scale (3030362880 : Int) atom0601)) (SparsePolynomial.merge (SparsePolynomial.scale (3046490880 : Int) atom0602) (SparsePolynomial.merge (SparsePolynomial.scale (3149441280 : Int) atom0603) (SparsePolynomial.scale (5212569600 : Int) atom0604))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4254706080 : Int) atom0605) (SparsePolynomial.scale (6153409440 : Int) atom0606)) (SparsePolynomial.merge (SparsePolynomial.scale (6238153440 : Int) atom0607) (SparsePolynomial.merge (SparsePolynomial.scale (7522604640 : Int) atom0608) (SparsePolynomial.scale (8807055840 : Int) atom0609)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2272957440 : Int) atom0610) (SparsePolynomial.scale (4097118720 : Int) atom0611)) (SparsePolynomial.merge (SparsePolynomial.scale (4015833600 : Int) atom0612) (SparsePolynomial.merge (SparsePolynomial.scale (4021370880 : Int) atom0613) (SparsePolynomial.scale (5867258880 : Int) atom0614))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5037388800 : Int) atom0615) (SparsePolynomial.scale (7210653600 : Int) atom0616)) (SparsePolynomial.merge (SparsePolynomial.scale (7037168640 : Int) atom0617) (SparsePolynomial.merge (SparsePolynomial.scale (8364979200 : Int) atom0618) (SparsePolynomial.scale (9692789760 : Int) atom0619)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2809259520 : Int) atom0620) (SparsePolynomial.scale (5038786560 : Int) atom0621)) (SparsePolynomial.merge (SparsePolynomial.scale (4896591360 : Int) atom0622) (SparsePolynomial.merge (SparsePolynomial.scale (6618561600 : Int) atom0623) (SparsePolynomial.scale (5688588480 : Int) atom0624))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8147367840 : Int) atom0625) (SparsePolynomial.scale (7535791680 : Int) atom0626)) (SparsePolynomial.merge (SparsePolynomial.scale (8811128640 : Int) atom0627) (SparsePolynomial.merge (SparsePolynomial.scale (10086465600 : Int) atom0628) (SparsePolynomial.scale (3318489600 : Int) atom0629)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5962744320 : Int) atom0630) (SparsePolynomial.scale (7475643840 : Int) atom0631)) (SparsePolynomial.merge (SparsePolynomial.scale (6325581120 : Int) atom0632) (SparsePolynomial.merge (SparsePolynomial.scale (9134401440 : Int) atom0633) (SparsePolynomial.scale (7710567360 : Int) atom0634)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8743776960 : Int) atom0635) (SparsePolynomial.scale (10067742720 : Int) atom0636)) (SparsePolynomial.merge (SparsePolynomial.scale (4066836480 : Int) atom0637) (SparsePolynomial.merge (SparsePolynomial.scale (8253020160 : Int) atom0638) (SparsePolynomial.scale (6758277120 : Int) atom0639)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9891879840 : Int) atom0640) (SparsePolynomial.scale (8512035840 : Int) atom0641)) (SparsePolynomial.merge (SparsePolynomial.scale (8191733760 : Int) atom0642) (SparsePolynomial.merge (SparsePolynomial.scale (11444912640 : Int) atom0643) (SparsePolynomial.scale (5763502080 : Int) atom0644))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9752279040 : Int) atom0645) (SparsePolynomial.scale (14480618400 : Int) atom0646)) (SparsePolynomial.merge (SparsePolynomial.scale (13034649600 : Int) atom0647) (SparsePolynomial.merge (SparsePolynomial.scale (8457523200 : Int) atom0648) (SparsePolynomial.scale (12763699200 : Int) atom0649)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4178055168 : Int) atom0650) (SparsePolynomial.scale (11741697720 : Int) atom0651)) (SparsePolynomial.merge (SparsePolynomial.scale (11815050240 : Int) atom0652) (SparsePolynomial.merge (SparsePolynomial.scale (8173670400 : Int) atom0653) (SparsePolynomial.scale (9910817280 : Int) atom0654)))))))) := by decide +kernel
theorem block008_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block008 := by
  rw [block008_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0575_nonneg g hg hA hB) (atom0576_nonneg g hg hA hB)) (add_nonneg (atom0577_nonneg g hg hA hB) (add_nonneg (atom0578_nonneg g hg hA hB) (atom0579_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0580_nonneg g hg hA hB) (atom0581_nonneg g hg hA hB)) (add_nonneg (atom0582_nonneg g hg hA hB) (add_nonneg (atom0583_nonneg g hg hA hB) (atom0584_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0585_nonneg g hg hA hB) (atom0586_nonneg g hg hA hB)) (add_nonneg (atom0587_nonneg g hg hA hB) (add_nonneg (atom0588_nonneg g hg hA hB) (atom0589_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0590_nonneg g hg hA hB) (atom0591_nonneg g hg hA hB)) (add_nonneg (atom0592_nonneg g hg hA hB) (add_nonneg (atom0593_nonneg g hg hA hB) (atom0594_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0595_nonneg g hg hA hB) (atom0596_nonneg g hg hA hB)) (add_nonneg (atom0597_nonneg g hg hA hB) (add_nonneg (atom0598_nonneg g hg hA hB) (atom0599_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0600_nonneg g hg hA hB) (atom0601_nonneg g hg hA hB)) (add_nonneg (atom0602_nonneg g hg hA hB) (add_nonneg (atom0603_nonneg g hg hA hB) (atom0604_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0605_nonneg g hg hA hB) (atom0606_nonneg g hg hA hB)) (add_nonneg (atom0607_nonneg g hg hA hB) (add_nonneg (atom0608_nonneg g hg hA hB) (atom0609_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0610_nonneg g hg hA hB) (atom0611_nonneg g hg hA hB)) (add_nonneg (atom0612_nonneg g hg hA hB) (add_nonneg (atom0613_nonneg g hg hA hB) (atom0614_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0615_nonneg g hg hA hB) (atom0616_nonneg g hg hA hB)) (add_nonneg (atom0617_nonneg g hg hA hB) (add_nonneg (atom0618_nonneg g hg hA hB) (atom0619_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0620_nonneg g hg hA hB) (atom0621_nonneg g hg hA hB)) (add_nonneg (atom0622_nonneg g hg hA hB) (add_nonneg (atom0623_nonneg g hg hA hB) (atom0624_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0625_nonneg g hg hA hB) (atom0626_nonneg g hg hA hB)) (add_nonneg (atom0627_nonneg g hg hA hB) (add_nonneg (atom0628_nonneg g hg hA hB) (atom0629_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0630_nonneg g hg hA hB) (atom0631_nonneg g hg hA hB)) (add_nonneg (atom0632_nonneg g hg hA hB) (add_nonneg (atom0633_nonneg g hg hA hB) (atom0634_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0635_nonneg g hg hA hB) (atom0636_nonneg g hg hA hB)) (add_nonneg (atom0637_nonneg g hg hA hB) (add_nonneg (atom0638_nonneg g hg hA hB) (atom0639_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0640_nonneg g hg hA hB) (atom0641_nonneg g hg hA hB)) (add_nonneg (atom0642_nonneg g hg hA hB) (add_nonneg (atom0643_nonneg g hg hA hB) (atom0644_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0645_nonneg g hg hA hB) (atom0646_nonneg g hg hA hB)) (add_nonneg (atom0647_nonneg g hg hA hB) (add_nonneg (atom0648_nonneg g hg hA hB) (atom0649_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0650_nonneg g hg hA hB) (atom0651_nonneg g hg hA hB)) (add_nonneg (atom0652_nonneg g hg hA hB) (add_nonneg (atom0653_nonneg g hg hA hB) (atom0654_nonneg g hg hA hB))))))))

end APPT.Finite18
