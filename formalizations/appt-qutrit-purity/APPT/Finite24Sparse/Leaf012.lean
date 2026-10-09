import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0769 : SparsePolynomial.Poly := [([1,20,20], 1)]
theorem eval_atom0769 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0769 = ((g 1) * (g 20) * (g 20)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0769_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (279004540953600 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770 : SparsePolynomial.Poly := [([1,20,21], 1)]
theorem eval_atom0770 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0770 = ((g 1) * (g 20) * (g 21)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0770_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (444567363609600 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771 : SparsePolynomial.Poly := [([1,20,22], 1)]
theorem eval_atom0771 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0771 = ((g 1) * (g 20) * (g 22)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0771_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (345540443942400 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772 : SparsePolynomial.Poly := [([1,20,23], 1)]
theorem eval_atom0772 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0772 = ((g 1) * (g 20) * (g 23)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0772_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (358952744304000 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773 : SparsePolynomial.Poly := [([1,21,21], 1)]
theorem eval_atom0773 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0773 = ((g 1) * (g 21) * (g 21)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0773_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158851007884800 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774 : SparsePolynomial.Poly := [([1,21,22], 1)]
theorem eval_atom0774 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0774 = ((g 1) * (g 21) * (g 22)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0774_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (218610772128000 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775 : SparsePolynomial.Poly := [([1,21,23], 1)]
theorem eval_atom0775 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0775 = ((g 1) * (g 21) * (g 23)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0775_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225802600531200 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776 : SparsePolynomial.Poly := [([1,22,22], 1)]
theorem eval_atom0776 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0776 = ((g 1) * (g 22) * (g 22)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0776_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36833126568000 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777 : SparsePolynomial.Poly := [([1,22,23], 1)]
theorem eval_atom0777 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0777 = ((g 1) * (g 22) * (g 23)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0777_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (80799180537600 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778 : SparsePolynomial.Poly := [([1,23,23], 1)]
theorem eval_atom0778 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0778 = ((g 1) * (g 23) * (g 23)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0778_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24047716492800 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0779 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0779 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0779_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42673534041600 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0780 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0780 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0780_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121833258624000 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0781 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0781 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0781_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (115645915123200 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0782 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0782 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0782_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116341465363200 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0783 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0783 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0783_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103271228121600 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784 : SparsePolynomial.Poly := [([2,2,7], 1)]
theorem eval_atom0784 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0784 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0784_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (97083884620800 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0785 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0785 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0785_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90896541120000 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786 : SparsePolynomial.Poly := [([2,2,9], 1)]
theorem eval_atom0786 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0786 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0786_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90720978665328 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787 : SparsePolynomial.Poly := [([2,2,10], 1)]
theorem eval_atom0787 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0787 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0787_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102177132198768 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788 : SparsePolynomial.Poly := [([2,2,11], 1)]
theorem eval_atom0788 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0788 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0788_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (111994858492704 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789 : SparsePolynomial.Poly := [([2,2,12], 1)]
theorem eval_atom0789 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0789 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0789_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (133729497215424 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790 : SparsePolynomial.Poly := [([2,2,13], 1)]
theorem eval_atom0790 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0790 = ((g 2) * (g 2) * (g 13)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0790_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (118881023184000 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791 : SparsePolynomial.Poly := [([2,2,14], 1)]
theorem eval_atom0791 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0791 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0791_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (100358286336000 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792 : SparsePolynomial.Poly := [([2,2,15], 1)]
theorem eval_atom0792 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0792 = ((g 2) * (g 2) * (g 15)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0792_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96622556083200 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793 : SparsePolynomial.Poly := [([2,2,16], 1)]
theorem eval_atom0793 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0793 = ((g 2) * (g 2) * (g 16)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0793_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81064315584000 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794 : SparsePolynomial.Poly := [([2,2,17], 1)]
theorem eval_atom0794 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0794 = ((g 2) * (g 2) * (g 17)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0794_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75438813542400 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795 : SparsePolynomial.Poly := [([2,2,18], 1)]
theorem eval_atom0795 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0795 = ((g 2) * (g 2) * (g 18)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0795_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99444005337600 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796 : SparsePolynomial.Poly := [([2,2,19], 1)]
theorem eval_atom0796 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0796 = ((g 2) * (g 2) * (g 19)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0796_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22835762611200 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797 : SparsePolynomial.Poly := [([2,2,20], 1)]
theorem eval_atom0797 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0797 = ((g 2) * (g 2) * (g 20)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0797_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (87069318336000 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798 : SparsePolynomial.Poly := [([2,2,21], 1)]
theorem eval_atom0798 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0798 = ((g 2) * (g 2) * (g 21)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0798_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10461075609600 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799 : SparsePolynomial.Poly := [([2,2,23], 1)]
theorem eval_atom0799 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0799 = ((g 2) * (g 2) * (g 23)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0799_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22272310368000 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 2) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0800 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0800 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0800_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (106396793395200 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0801 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0801 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0801_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203480678016000 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0802 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0802 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0802_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207933556723200 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0803 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0803 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0803_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (184854860467200 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0804 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0804 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0804_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175541951692800 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0805 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0805 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0805_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166229042918400 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806 : SparsePolynomial.Poly := [([2,3,9], 1)]
theorem eval_atom0806 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0806 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0806_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (168939696236256 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807 : SparsePolynomial.Poly := [([2,3,10], 1)]
theorem eval_atom0807 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0807 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0807_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (194913781530336 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808 : SparsePolynomial.Poly := [([2,3,11], 1)]
theorem eval_atom0808 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0808 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0808_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (217611012345408 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809 : SparsePolynomial.Poly := [([2,3,12], 1)]
theorem eval_atom0809 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0809 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0809_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264142068018048 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810 : SparsePolynomial.Poly := [([2,3,13], 1)]
theorem eval_atom0810 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0810 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0810_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (237506898182400 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811 : SparsePolynomial.Poly := [([2,3,14], 1)]
theorem eval_atom0811 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0811 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0811_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203523202713600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812 : SparsePolynomial.Poly := [([2,3,15], 1)]
theorem eval_atom0812 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0812 = ((g 2) * (g 3) * (g 15)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0812_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (199113520435200 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813 : SparsePolynomial.Poly := [([2,3,16], 1)]
theorem eval_atom0813 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0813 = ((g 2) * (g 3) * (g 16)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0813_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171058817664000 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814 : SparsePolynomial.Poly := [([2,3,17], 1)]
theorem eval_atom0814 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0814 = ((g 2) * (g 3) * (g 17)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0814_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (162869591808000 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0815 : SparsePolynomial.Poly := [([2,3,18], 1)]
theorem eval_atom0815 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0815 = ((g 2) * (g 3) * (g 18)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0815_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (213941753625600 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0816 : SparsePolynomial.Poly := [([2,3,19], 1)]
theorem eval_atom0816 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0816 = ((g 2) * (g 3) * (g 19)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0816_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91683248025600 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817 : SparsePolynomial.Poly := [([2,3,20], 1)]
theorem eval_atom0817 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0817 = ((g 2) * (g 3) * (g 20)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0817_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (195315936076800 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818 : SparsePolynomial.Poly := [([2,3,21], 1)]
theorem eval_atom0818 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0818 = ((g 2) * (g 3) * (g 21)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0818_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (85474642176000 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819 : SparsePolynomial.Poly := [([2,3,22], 1)]
theorem eval_atom0819 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0819 = ((g 2) * (g 3) * (g 22)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0819_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78096607142400 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820 : SparsePolynomial.Poly := [([2,3,23], 1)]
theorem eval_atom0820 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0820 = ((g 2) * (g 3) * (g 23)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0820_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103451958086400 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0821 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0821 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0821_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105130072857600 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0822 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0822 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0822_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (191950417603296 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0823 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0823 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0823_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163167264691200 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0824 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0824 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0824_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156916134144000 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0825 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0825 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0825_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150665003596800 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826 : SparsePolynomial.Poly := [([2,4,9], 1)]
theorem eval_atom0826 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0826 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0826_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156437435141856 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827 : SparsePolynomial.Poly := [([2,4,10], 1)]
theorem eval_atom0827 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0827 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0827_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (185473298663136 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828 : SparsePolynomial.Poly := [([2,4,11], 1)]
theorem eval_atom0828 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0828 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0828_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211232307705408 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829 : SparsePolynomial.Poly := [([2,4,12], 1)]
theorem eval_atom0829 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0829 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0829_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (260825141605248 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830 : SparsePolynomial.Poly := [([2,4,13], 1)]
theorem eval_atom0830 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0830 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0830_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (237251749996800 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831 : SparsePolynomial.Poly := [([2,4,14], 1)]
theorem eval_atom0831 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0831 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0831_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (206329832755200 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832 : SparsePolynomial.Poly := [([2,4,15], 1)]
theorem eval_atom0832 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0832 = ((g 2) * (g 4) * (g 15)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0832_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (204981928704000 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833 : SparsePolynomial.Poly := [([2,4,16], 1)]
theorem eval_atom0833 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0833 = ((g 2) * (g 4) * (g 16)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0833_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (179989004160000 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834 : SparsePolynomial.Poly := [([2,4,17], 1)]
theorem eval_atom0834 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0834 = ((g 2) * (g 4) * (g 17)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0834_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (179508990528000 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835 : SparsePolynomial.Poly := [([2,4,18], 1)]
theorem eval_atom0835 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0835 = ((g 2) * (g 4) * (g 18)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0835_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (228995496576000 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836 : SparsePolynomial.Poly := [([2,4,19], 1)]
theorem eval_atom0836 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0836 = ((g 2) * (g 4) * (g 19)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0836_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (143682657652800 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837 : SparsePolynomial.Poly := [([2,4,20], 1)]
theorem eval_atom0837 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0837 = ((g 2) * (g 4) * (g 20)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0837_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (217385529278400 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838 : SparsePolynomial.Poly := [([2,4,21], 1)]
theorem eval_atom0838 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0838 = ((g 2) * (g 4) * (g 21)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0838_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (154570429944000 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839 : SparsePolynomial.Poly := [([2,4,22], 1)]
theorem eval_atom0839 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0839 = ((g 2) * (g 4) * (g 22)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0839_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157902497726400 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840 : SparsePolynomial.Poly := [([2,4,23], 1)]
theorem eval_atom0840 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0840 = ((g 2) * (g 4) * (g 23)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0840_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193967951486400 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0841 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0841 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0841_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121046551718400 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0842 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0842 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0842_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207642031017696 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0843 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0843 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0843_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (182965893993696 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0844 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0844 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0844_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (182850052502304 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845 : SparsePolynomial.Poly := [([2,5,9], 1)]
theorem eval_atom0845 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0845 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0845_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188053864294032 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846 : SparsePolynomial.Poly := [([2,5,10], 1)]
theorem eval_atom0846 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0846 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0846_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (199971722137968 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847 : SparsePolynomial.Poly := [([2,5,11], 1)]
theorem eval_atom0847 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0847 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0847_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (218619390547008 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848 : SparsePolynomial.Poly := [([2,5,12], 1)]
theorem eval_atom0848 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0848 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0848_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (271274002674048 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block012 : SparsePolynomial.Poly := [([1,20,20], 279004540953600), ([1,20,21], 444567363609600), ([1,20,22], 345540443942400), ([1,20,23], 358952744304000), ([1,21,21], 158851007884800), ([1,21,22], 218610772128000), ([1,21,23], 225802600531200), ([1,22,22], 36833126568000), ([1,22,23], 80799180537600), ([1,23,23], 24047716492800), ([2,2,2], 42673534041600), ([2,2,3], 121833258624000), ([2,2,4], 115645915123200), ([2,2,5], 116341465363200), ([2,2,6], 103271228121600), ([2,2,7], 97083884620800), ([2,2,8], 90896541120000), ([2,2,9], 90720978665328), ([2,2,10], 102177132198768), ([2,2,11], 111994858492704), ([2,2,12], 133729497215424), ([2,2,13], 118881023184000), ([2,2,14], 100358286336000), ([2,2,15], 96622556083200), ([2,2,16], 81064315584000), ([2,2,17], 75438813542400), ([2,2,18], 99444005337600), ([2,2,19], 22835762611200), ([2,2,20], 87069318336000), ([2,2,21], 10461075609600), ([2,2,23], 22272310368000), ([2,3,3], 106396793395200), ([2,3,4], 203480678016000), ([2,3,5], 207933556723200), ([2,3,6], 184854860467200), ([2,3,7], 175541951692800), ([2,3,8], 166229042918400), ([2,3,9], 168939696236256), ([2,3,10], 194913781530336), ([2,3,11], 217611012345408), ([2,3,12], 264142068018048), ([2,3,13], 237506898182400), ([2,3,14], 203523202713600), ([2,3,15], 199113520435200), ([2,3,16], 171058817664000), ([2,3,17], 162869591808000), ([2,3,18], 213941753625600), ([2,3,19], 91683248025600), ([2,3,20], 195315936076800), ([2,3,21], 85474642176000), ([2,3,22], 78096607142400), ([2,3,23], 103451958086400), ([2,4,4], 105130072857600), ([2,4,5], 191950417603296), ([2,4,6], 163167264691200), ([2,4,7], 156916134144000), ([2,4,8], 150665003596800), ([2,4,9], 156437435141856), ([2,4,10], 185473298663136), ([2,4,11], 211232307705408), ([2,4,12], 260825141605248), ([2,4,13], 237251749996800), ([2,4,14], 206329832755200), ([2,4,15], 204981928704000), ([2,4,16], 179989004160000), ([2,4,17], 179508990528000), ([2,4,18], 228995496576000), ([2,4,19], 143682657652800), ([2,4,20], 217385529278400), ([2,4,21], 154570429944000), ([2,4,22], 157902497726400), ([2,4,23], 193967951486400), ([2,5,5], 121046551718400), ([2,5,6], 207642031017696), ([2,5,7], 182965893993696), ([2,5,8], 182850052502304), ([2,5,9], 188053864294032), ([2,5,10], 199971722137968), ([2,5,11], 218619390547008), ([2,5,12], 271274002674048)]
theorem block012_data : block012 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (279004540953600 : Int) atom0769) (SparsePolynomial.scale (444567363609600 : Int) atom0770)) (SparsePolynomial.merge (SparsePolynomial.scale (345540443942400 : Int) atom0771) (SparsePolynomial.merge (SparsePolynomial.scale (358952744304000 : Int) atom0772) (SparsePolynomial.scale (158851007884800 : Int) atom0773)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (218610772128000 : Int) atom0774) (SparsePolynomial.scale (225802600531200 : Int) atom0775)) (SparsePolynomial.merge (SparsePolynomial.scale (36833126568000 : Int) atom0776) (SparsePolynomial.merge (SparsePolynomial.scale (80799180537600 : Int) atom0777) (SparsePolynomial.scale (24047716492800 : Int) atom0778))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (42673534041600 : Int) atom0779) (SparsePolynomial.scale (121833258624000 : Int) atom0780)) (SparsePolynomial.merge (SparsePolynomial.scale (115645915123200 : Int) atom0781) (SparsePolynomial.merge (SparsePolynomial.scale (116341465363200 : Int) atom0782) (SparsePolynomial.scale (103271228121600 : Int) atom0783)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (97083884620800 : Int) atom0784) (SparsePolynomial.scale (90896541120000 : Int) atom0785)) (SparsePolynomial.merge (SparsePolynomial.scale (90720978665328 : Int) atom0786) (SparsePolynomial.merge (SparsePolynomial.scale (102177132198768 : Int) atom0787) (SparsePolynomial.scale (111994858492704 : Int) atom0788)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (133729497215424 : Int) atom0789) (SparsePolynomial.scale (118881023184000 : Int) atom0790)) (SparsePolynomial.merge (SparsePolynomial.scale (100358286336000 : Int) atom0791) (SparsePolynomial.merge (SparsePolynomial.scale (96622556083200 : Int) atom0792) (SparsePolynomial.scale (81064315584000 : Int) atom0793)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (75438813542400 : Int) atom0794) (SparsePolynomial.scale (99444005337600 : Int) atom0795)) (SparsePolynomial.merge (SparsePolynomial.scale (22835762611200 : Int) atom0796) (SparsePolynomial.merge (SparsePolynomial.scale (87069318336000 : Int) atom0797) (SparsePolynomial.scale (10461075609600 : Int) atom0798))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22272310368000 : Int) atom0799) (SparsePolynomial.scale (106396793395200 : Int) atom0800)) (SparsePolynomial.merge (SparsePolynomial.scale (203480678016000 : Int) atom0801) (SparsePolynomial.merge (SparsePolynomial.scale (207933556723200 : Int) atom0802) (SparsePolynomial.scale (184854860467200 : Int) atom0803)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (175541951692800 : Int) atom0804) (SparsePolynomial.scale (166229042918400 : Int) atom0805)) (SparsePolynomial.merge (SparsePolynomial.scale (168939696236256 : Int) atom0806) (SparsePolynomial.merge (SparsePolynomial.scale (194913781530336 : Int) atom0807) (SparsePolynomial.scale (217611012345408 : Int) atom0808))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (264142068018048 : Int) atom0809) (SparsePolynomial.scale (237506898182400 : Int) atom0810)) (SparsePolynomial.merge (SparsePolynomial.scale (203523202713600 : Int) atom0811) (SparsePolynomial.merge (SparsePolynomial.scale (199113520435200 : Int) atom0812) (SparsePolynomial.scale (171058817664000 : Int) atom0813)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (162869591808000 : Int) atom0814) (SparsePolynomial.scale (213941753625600 : Int) atom0815)) (SparsePolynomial.merge (SparsePolynomial.scale (91683248025600 : Int) atom0816) (SparsePolynomial.merge (SparsePolynomial.scale (195315936076800 : Int) atom0817) (SparsePolynomial.scale (85474642176000 : Int) atom0818))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (78096607142400 : Int) atom0819) (SparsePolynomial.scale (103451958086400 : Int) atom0820)) (SparsePolynomial.merge (SparsePolynomial.scale (105130072857600 : Int) atom0821) (SparsePolynomial.merge (SparsePolynomial.scale (191950417603296 : Int) atom0822) (SparsePolynomial.scale (163167264691200 : Int) atom0823)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (156916134144000 : Int) atom0824) (SparsePolynomial.scale (150665003596800 : Int) atom0825)) (SparsePolynomial.merge (SparsePolynomial.scale (156437435141856 : Int) atom0826) (SparsePolynomial.merge (SparsePolynomial.scale (185473298663136 : Int) atom0827) (SparsePolynomial.scale (211232307705408 : Int) atom0828)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (260825141605248 : Int) atom0829) (SparsePolynomial.scale (237251749996800 : Int) atom0830)) (SparsePolynomial.merge (SparsePolynomial.scale (206329832755200 : Int) atom0831) (SparsePolynomial.merge (SparsePolynomial.scale (204981928704000 : Int) atom0832) (SparsePolynomial.scale (179989004160000 : Int) atom0833)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (179508990528000 : Int) atom0834) (SparsePolynomial.scale (228995496576000 : Int) atom0835)) (SparsePolynomial.merge (SparsePolynomial.scale (143682657652800 : Int) atom0836) (SparsePolynomial.merge (SparsePolynomial.scale (217385529278400 : Int) atom0837) (SparsePolynomial.scale (154570429944000 : Int) atom0838))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (157902497726400 : Int) atom0839) (SparsePolynomial.scale (193967951486400 : Int) atom0840)) (SparsePolynomial.merge (SparsePolynomial.scale (121046551718400 : Int) atom0841) (SparsePolynomial.merge (SparsePolynomial.scale (207642031017696 : Int) atom0842) (SparsePolynomial.scale (182965893993696 : Int) atom0843)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (182850052502304 : Int) atom0844) (SparsePolynomial.scale (188053864294032 : Int) atom0845)) (SparsePolynomial.merge (SparsePolynomial.scale (199971722137968 : Int) atom0846) (SparsePolynomial.merge (SparsePolynomial.scale (218619390547008 : Int) atom0847) (SparsePolynomial.scale (271274002674048 : Int) atom0848)))))))) := by decide +kernel
theorem block012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block012 := by
  rw [block012_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0769_nonneg g hg hA hB) (atom0770_nonneg g hg hA hB)) (add_nonneg (atom0771_nonneg g hg hA hB) (add_nonneg (atom0772_nonneg g hg hA hB) (atom0773_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0774_nonneg g hg hA hB) (atom0775_nonneg g hg hA hB)) (add_nonneg (atom0776_nonneg g hg hA hB) (add_nonneg (atom0777_nonneg g hg hA hB) (atom0778_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0779_nonneg g hg hA hB) (atom0780_nonneg g hg hA hB)) (add_nonneg (atom0781_nonneg g hg hA hB) (add_nonneg (atom0782_nonneg g hg hA hB) (atom0783_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0784_nonneg g hg hA hB) (atom0785_nonneg g hg hA hB)) (add_nonneg (atom0786_nonneg g hg hA hB) (add_nonneg (atom0787_nonneg g hg hA hB) (atom0788_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0789_nonneg g hg hA hB) (atom0790_nonneg g hg hA hB)) (add_nonneg (atom0791_nonneg g hg hA hB) (add_nonneg (atom0792_nonneg g hg hA hB) (atom0793_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0794_nonneg g hg hA hB) (atom0795_nonneg g hg hA hB)) (add_nonneg (atom0796_nonneg g hg hA hB) (add_nonneg (atom0797_nonneg g hg hA hB) (atom0798_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0799_nonneg g hg hA hB) (atom0800_nonneg g hg hA hB)) (add_nonneg (atom0801_nonneg g hg hA hB) (add_nonneg (atom0802_nonneg g hg hA hB) (atom0803_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0804_nonneg g hg hA hB) (atom0805_nonneg g hg hA hB)) (add_nonneg (atom0806_nonneg g hg hA hB) (add_nonneg (atom0807_nonneg g hg hA hB) (atom0808_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0809_nonneg g hg hA hB) (atom0810_nonneg g hg hA hB)) (add_nonneg (atom0811_nonneg g hg hA hB) (add_nonneg (atom0812_nonneg g hg hA hB) (atom0813_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0814_nonneg g hg hA hB) (atom0815_nonneg g hg hA hB)) (add_nonneg (atom0816_nonneg g hg hA hB) (add_nonneg (atom0817_nonneg g hg hA hB) (atom0818_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0819_nonneg g hg hA hB) (atom0820_nonneg g hg hA hB)) (add_nonneg (atom0821_nonneg g hg hA hB) (add_nonneg (atom0822_nonneg g hg hA hB) (atom0823_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0824_nonneg g hg hA hB) (atom0825_nonneg g hg hA hB)) (add_nonneg (atom0826_nonneg g hg hA hB) (add_nonneg (atom0827_nonneg g hg hA hB) (atom0828_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0829_nonneg g hg hA hB) (atom0830_nonneg g hg hA hB)) (add_nonneg (atom0831_nonneg g hg hA hB) (add_nonneg (atom0832_nonneg g hg hA hB) (atom0833_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0834_nonneg g hg hA hB) (atom0835_nonneg g hg hA hB)) (add_nonneg (atom0836_nonneg g hg hA hB) (add_nonneg (atom0837_nonneg g hg hA hB) (atom0838_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0839_nonneg g hg hA hB) (atom0840_nonneg g hg hA hB)) (add_nonneg (atom0841_nonneg g hg hA hB) (add_nonneg (atom0842_nonneg g hg hA hB) (atom0843_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0844_nonneg g hg hA hB) (atom0845_nonneg g hg hA hB)) (add_nonneg (atom0846_nonneg g hg hA hB) (add_nonneg (atom0847_nonneg g hg hA hB) (atom0848_nonneg g hg hA hB))))))))

end APPT.Finite24
