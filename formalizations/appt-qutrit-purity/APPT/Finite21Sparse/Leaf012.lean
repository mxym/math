import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0816 : SparsePolynomial.Poly := [([3,6,15], 1)]
theorem eval_atom0816 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0816 = ((g 3) * (g 6) * (g 15)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0816_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24718775961600 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817 : SparsePolynomial.Poly := [([3,6,16], 1)]
theorem eval_atom0817 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0817 = ((g 3) * (g 6) * (g 16)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0817_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16729808256000 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818 : SparsePolynomial.Poly := [([3,6,17], 1)]
theorem eval_atom0818 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0818 = ((g 3) * (g 6) * (g 17)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0818_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23887200153600 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819 : SparsePolynomial.Poly := [([3,6,18], 1)]
theorem eval_atom0819 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0819 = ((g 3) * (g 6) * (g 18)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0819_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25103061043200 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820 : SparsePolynomial.Poly := [([3,6,19], 1)]
theorem eval_atom0820 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0820 = ((g 3) * (g 6) * (g 19)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0820_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30426215500800 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821 : SparsePolynomial.Poly := [([3,6,20], 1)]
theorem eval_atom0821 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0821 = ((g 3) * (g 6) * (g 20)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0821_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35749369958400 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0822 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13525981519104 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0823 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0823 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0823_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23968533112704 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824 : SparsePolynomial.Poly := [([3,7,9], 1)]
theorem eval_atom0824 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0824 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0824_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21615660923904 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825 : SparsePolynomial.Poly := [([3,7,10], 1)]
theorem eval_atom0825 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0825 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0825_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21699743848704 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826 : SparsePolynomial.Poly := [([3,7,11], 1)]
theorem eval_atom0826 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0826 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0826_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21730917256704 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827 : SparsePolynomial.Poly := [([3,7,12], 1)]
theorem eval_atom0827 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0827 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0827_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19796620450304 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828 : SparsePolynomial.Poly := [([3,7,13], 1)]
theorem eval_atom0828 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0828 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0828_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19605402491904 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829 : SparsePolynomial.Poly := [([3,7,14], 1)]
theorem eval_atom0829 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0829 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0829_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20291596475904 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830 : SparsePolynomial.Poly := [([3,7,15], 1)]
theorem eval_atom0830 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0830 = ((g 3) * (g 7) * (g 15)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0830_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30208777521408 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831 : SparsePolynomial.Poly := [([3,7,16], 1)]
theorem eval_atom0831 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0831 = ((g 3) * (g 7) * (g 16)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0831_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22810615971840 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832 : SparsePolynomial.Poly := [([3,7,17], 1)]
theorem eval_atom0832 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0832 = ((g 3) * (g 7) * (g 17)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0832_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30722528510208 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833 : SparsePolynomial.Poly := [([3,7,18], 1)]
theorem eval_atom0833 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0833 = ((g 3) * (g 7) * (g 18)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0833_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30744200282112 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834 : SparsePolynomial.Poly := [([3,7,19], 1)]
theorem eval_atom0834 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0834 = ((g 3) * (g 7) * (g 19)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0834_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35800014965760 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835 : SparsePolynomial.Poly := [([3,7,20], 1)]
theorem eval_atom0835 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0835 = ((g 3) * (g 7) * (g 20)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0835_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40855829649408 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0836 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15309696528000 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837 : SparsePolynomial.Poly := [([3,8,9], 1)]
theorem eval_atom0837 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0837 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0837_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28111885603200 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838 : SparsePolynomial.Poly := [([3,8,10], 1)]
theorem eval_atom0838 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0838 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0838_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27691470979200 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839 : SparsePolynomial.Poly := [([3,8,11], 1)]
theorem eval_atom0839 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0839 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0839_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27218146838400 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840 : SparsePolynomial.Poly := [([3,8,12], 1)]
theorem eval_atom0840 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0840 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0840_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24611186633600 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841 : SparsePolynomial.Poly := [([3,8,13], 1)]
theorem eval_atom0841 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0841 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0841_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24174485193600 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842 : SparsePolynomial.Poly := [([3,8,14], 1)]
theorem eval_atom0842 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0842 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0842_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24615195696000 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843 : SparsePolynomial.Poly := [([3,8,15], 1)]
theorem eval_atom0843 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0843 = ((g 3) * (g 8) * (g 15)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0843_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33795536947200 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844 : SparsePolynomial.Poly := [([3,8,16], 1)]
theorem eval_atom0844 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0844 = ((g 3) * (g 8) * (g 16)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0844_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27092078118000 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845 : SparsePolynomial.Poly := [([3,8,17], 1)]
theorem eval_atom0845 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0845 = ((g 3) * (g 8) * (g 17)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0845_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35654614732800 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846 : SparsePolynomial.Poly := [([3,8,18], 1)]
theorem eval_atom0846 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0846 = ((g 3) * (g 8) * (g 18)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0846_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35432355243600 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847 : SparsePolynomial.Poly := [([3,8,19], 1)]
theorem eval_atom0847 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0847 = ((g 3) * (g 8) * (g 19)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0847_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40841126298000 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848 : SparsePolynomial.Poly := [([3,8,20], 1)]
theorem eval_atom0848 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0848 = ((g 3) * (g 8) * (g 20)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0848_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46249897352400 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom0849 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17669334009600 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850 : SparsePolynomial.Poly := [([3,9,10], 1)]
theorem eval_atom0850 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32970815539200 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851 : SparsePolynomial.Poly := [([3,9,11], 1)]
theorem eval_atom0851 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31824828000000 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852 : SparsePolynomial.Poly := [([3,9,12], 1)]
theorem eval_atom0852 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29231398380800 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853 : SparsePolynomial.Poly := [([3,9,13], 1)]
theorem eval_atom0853 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28381047609600 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854 : SparsePolynomial.Poly := [([3,9,14], 1)]
theorem eval_atom0854 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28408108780800 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855 : SparsePolynomial.Poly := [([3,9,15], 1)]
theorem eval_atom0855 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 3) * (g 9) * (g 15)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37232305689600 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856 : SparsePolynomial.Poly := [([3,9,16], 1)]
theorem eval_atom0856 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 3) * (g 9) * (g 16)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30526491088800 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857 : SparsePolynomial.Poly := [([3,9,17], 1)]
theorem eval_atom0857 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 3) * (g 9) * (g 17)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40436710272000 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858 : SparsePolynomial.Poly := [([3,9,18], 1)]
theorem eval_atom0858 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 3) * (g 9) * (g 18)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38977066648800 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859 : SparsePolynomial.Poly := [([3,9,19], 1)]
theorem eval_atom0859 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 3) * (g 9) * (g 19)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44597253103200 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860 : SparsePolynomial.Poly := [([3,9,20], 1)]
theorem eval_atom0860 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 3) * (g 9) * (g 20)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50217439557600 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom0861 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20168626464000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862 : SparsePolynomial.Poly := [([3,10,11], 1)]
theorem eval_atom0862 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37845938592000 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863 : SparsePolynomial.Poly := [([3,10,12], 1)]
theorem eval_atom0863 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34243513875200 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864 : SparsePolynomial.Poly := [([3,10,13], 1)]
theorem eval_atom0864 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32811347923200 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865 : SparsePolynomial.Poly := [([3,10,14], 1)]
theorem eval_atom0865 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32256593913600 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866 : SparsePolynomial.Poly := [([3,10,15], 1)]
theorem eval_atom0866 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 3) * (g 10) * (g 15)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40669074432000 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867 : SparsePolynomial.Poly := [([3,10,16], 1)]
theorem eval_atom0867 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 3) * (g 10) * (g 16)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33480266248800 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868 : SparsePolynomial.Poly := [([3,10,17], 1)]
theorem eval_atom0868 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 3) * (g 10) * (g 17)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45218805811200 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869 : SparsePolynomial.Poly := [([3,10,18], 1)]
theorem eval_atom0869 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 3) * (g 10) * (g 18)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41305052224800 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870 : SparsePolynomial.Poly := [([3,10,19], 1)]
theorem eval_atom0870 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 3) * (g 10) * (g 19)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46701984016800 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871 : SparsePolynomial.Poly := [([3,10,20], 1)]
theorem eval_atom0871 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 3) * (g 10) * (g 20)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52098915808800 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom0872 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22544457062400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873 : SparsePolynomial.Poly := [([3,11,12], 1)]
theorem eval_atom0873 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39286802777600 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874 : SparsePolynomial.Poly := [([3,11,13], 1)]
theorem eval_atom0874 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37104655795200 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875 : SparsePolynomial.Poly := [([3,11,14], 1)]
theorem eval_atom0875 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35799920755200 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876 : SparsePolynomial.Poly := [([3,11,15], 1)]
theorem eval_atom0876 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 3) * (g 11) * (g 15)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43481996006400 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877 : SparsePolynomial.Poly := [([3,11,16], 1)]
theorem eval_atom0877 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 3) * (g 11) * (g 16)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35727947136000 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878 : SparsePolynomial.Poly := [([3,11,17], 1)]
theorem eval_atom0878 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 3) * (g 11) * (g 17)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49377054182400 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879 : SparsePolynomial.Poly := [([3,11,18], 1)]
theorem eval_atom0879 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 3) * (g 11) * (g 18)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42461403264000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880 : SparsePolynomial.Poly := [([3,11,19], 1)]
theorem eval_atom0880 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 3) * (g 11) * (g 19)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47380775500800 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881 : SparsePolynomial.Poly := [([3,11,20], 1)]
theorem eval_atom0881 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 3) * (g 11) * (g 20)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52300147737600 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882 : SparsePolynomial.Poly := [([3,12,12], 1)]
theorem eval_atom0882 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22036670566400 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883 : SparsePolynomial.Poly := [([3,12,13], 1)]
theorem eval_atom0883 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40545867353600 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884 : SparsePolynomial.Poly := [([3,12,14], 1)]
theorem eval_atom0884 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38322985433600 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885 : SparsePolynomial.Poly := [([3,12,15], 1)]
theorem eval_atom0885 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 3) * (g 12) * (g 15)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42195811302400 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886 : SparsePolynomial.Poly := [([3,12,16], 1)]
theorem eval_atom0886 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 3) * (g 12) * (g 16)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36822593830400 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887 : SparsePolynomial.Poly := [([3,12,17], 1)]
theorem eval_atom0887 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 3) * (g 12) * (g 17)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49436196275200 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888 : SparsePolynomial.Poly := [([3,12,18], 1)]
theorem eval_atom0888 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 3) * (g 12) * (g 18)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43193208755200 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889 : SparsePolynomial.Poly := [([3,12,19], 1)]
theorem eval_atom0889 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 3) * (g 12) * (g 19)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47080567475200 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890 : SparsePolynomial.Poly := [([3,12,20], 1)]
theorem eval_atom0890 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 3) * (g 12) * (g 20)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51625627200000 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891 : SparsePolynomial.Poly := [([3,13,13], 1)]
theorem eval_atom0891 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23512015756800 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892 : SparsePolynomial.Poly := [([3,13,14], 1)]
theorem eval_atom0892 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42544303142400 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893 : SparsePolynomial.Poly := [([3,13,15], 1)]
theorem eval_atom0893 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 3) * (g 13) * (g 15)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45194813697600 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894 : SparsePolynomial.Poly := [([3,13,16], 1)]
theorem eval_atom0894 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 3) * (g 13) * (g 16)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38463278328000 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895 : SparsePolynomial.Poly := [([3,13,17], 1)]
theorem eval_atom0895 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 3) * (g 13) * (g 17)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52981496064000 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block012 : SparsePolynomial.Poly := [([3,6,15], 24718775961600), ([3,6,16], 16729808256000), ([3,6,17], 23887200153600), ([3,6,18], 25103061043200), ([3,6,19], 30426215500800), ([3,6,20], 35749369958400), ([3,7,7], 13525981519104), ([3,7,8], 23968533112704), ([3,7,9], 21615660923904), ([3,7,10], 21699743848704), ([3,7,11], 21730917256704), ([3,7,12], 19796620450304), ([3,7,13], 19605402491904), ([3,7,14], 20291596475904), ([3,7,15], 30208777521408), ([3,7,16], 22810615971840), ([3,7,17], 30722528510208), ([3,7,18], 30744200282112), ([3,7,19], 35800014965760), ([3,7,20], 40855829649408), ([3,8,8], 15309696528000), ([3,8,9], 28111885603200), ([3,8,10], 27691470979200), ([3,8,11], 27218146838400), ([3,8,12], 24611186633600), ([3,8,13], 24174485193600), ([3,8,14], 24615195696000), ([3,8,15], 33795536947200), ([3,8,16], 27092078118000), ([3,8,17], 35654614732800), ([3,8,18], 35432355243600), ([3,8,19], 40841126298000), ([3,8,20], 46249897352400), ([3,9,9], 17669334009600), ([3,9,10], 32970815539200), ([3,9,11], 31824828000000), ([3,9,12], 29231398380800), ([3,9,13], 28381047609600), ([3,9,14], 28408108780800), ([3,9,15], 37232305689600), ([3,9,16], 30526491088800), ([3,9,17], 40436710272000), ([3,9,18], 38977066648800), ([3,9,19], 44597253103200), ([3,9,20], 50217439557600), ([3,10,10], 20168626464000), ([3,10,11], 37845938592000), ([3,10,12], 34243513875200), ([3,10,13], 32811347923200), ([3,10,14], 32256593913600), ([3,10,15], 40669074432000), ([3,10,16], 33480266248800), ([3,10,17], 45218805811200), ([3,10,18], 41305052224800), ([3,10,19], 46701984016800), ([3,10,20], 52098915808800), ([3,11,11], 22544457062400), ([3,11,12], 39286802777600), ([3,11,13], 37104655795200), ([3,11,14], 35799920755200), ([3,11,15], 43481996006400), ([3,11,16], 35727947136000), ([3,11,17], 49377054182400), ([3,11,18], 42461403264000), ([3,11,19], 47380775500800), ([3,11,20], 52300147737600), ([3,12,12], 22036670566400), ([3,12,13], 40545867353600), ([3,12,14], 38322985433600), ([3,12,15], 42195811302400), ([3,12,16], 36822593830400), ([3,12,17], 49436196275200), ([3,12,18], 43193208755200), ([3,12,19], 47080567475200), ([3,12,20], 51625627200000), ([3,13,13], 23512015756800), ([3,13,14], 42544303142400), ([3,13,15], 45194813697600), ([3,13,16], 38463278328000), ([3,13,17], 52981496064000)]
theorem block012_data : block012 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24718775961600 : Int) atom0816) (SparsePolynomial.scale (16729808256000 : Int) atom0817)) (SparsePolynomial.merge (SparsePolynomial.scale (23887200153600 : Int) atom0818) (SparsePolynomial.merge (SparsePolynomial.scale (25103061043200 : Int) atom0819) (SparsePolynomial.scale (30426215500800 : Int) atom0820)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35749369958400 : Int) atom0821) (SparsePolynomial.scale (13525981519104 : Int) atom0822)) (SparsePolynomial.merge (SparsePolynomial.scale (23968533112704 : Int) atom0823) (SparsePolynomial.merge (SparsePolynomial.scale (21615660923904 : Int) atom0824) (SparsePolynomial.scale (21699743848704 : Int) atom0825))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21730917256704 : Int) atom0826) (SparsePolynomial.scale (19796620450304 : Int) atom0827)) (SparsePolynomial.merge (SparsePolynomial.scale (19605402491904 : Int) atom0828) (SparsePolynomial.merge (SparsePolynomial.scale (20291596475904 : Int) atom0829) (SparsePolynomial.scale (30208777521408 : Int) atom0830)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22810615971840 : Int) atom0831) (SparsePolynomial.scale (30722528510208 : Int) atom0832)) (SparsePolynomial.merge (SparsePolynomial.scale (30744200282112 : Int) atom0833) (SparsePolynomial.merge (SparsePolynomial.scale (35800014965760 : Int) atom0834) (SparsePolynomial.scale (40855829649408 : Int) atom0835)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15309696528000 : Int) atom0836) (SparsePolynomial.scale (28111885603200 : Int) atom0837)) (SparsePolynomial.merge (SparsePolynomial.scale (27691470979200 : Int) atom0838) (SparsePolynomial.merge (SparsePolynomial.scale (27218146838400 : Int) atom0839) (SparsePolynomial.scale (24611186633600 : Int) atom0840)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24174485193600 : Int) atom0841) (SparsePolynomial.scale (24615195696000 : Int) atom0842)) (SparsePolynomial.merge (SparsePolynomial.scale (33795536947200 : Int) atom0843) (SparsePolynomial.merge (SparsePolynomial.scale (27092078118000 : Int) atom0844) (SparsePolynomial.scale (35654614732800 : Int) atom0845))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35432355243600 : Int) atom0846) (SparsePolynomial.scale (40841126298000 : Int) atom0847)) (SparsePolynomial.merge (SparsePolynomial.scale (46249897352400 : Int) atom0848) (SparsePolynomial.merge (SparsePolynomial.scale (17669334009600 : Int) atom0849) (SparsePolynomial.scale (32970815539200 : Int) atom0850)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31824828000000 : Int) atom0851) (SparsePolynomial.scale (29231398380800 : Int) atom0852)) (SparsePolynomial.merge (SparsePolynomial.scale (28381047609600 : Int) atom0853) (SparsePolynomial.merge (SparsePolynomial.scale (28408108780800 : Int) atom0854) (SparsePolynomial.scale (37232305689600 : Int) atom0855))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30526491088800 : Int) atom0856) (SparsePolynomial.scale (40436710272000 : Int) atom0857)) (SparsePolynomial.merge (SparsePolynomial.scale (38977066648800 : Int) atom0858) (SparsePolynomial.merge (SparsePolynomial.scale (44597253103200 : Int) atom0859) (SparsePolynomial.scale (50217439557600 : Int) atom0860)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20168626464000 : Int) atom0861) (SparsePolynomial.scale (37845938592000 : Int) atom0862)) (SparsePolynomial.merge (SparsePolynomial.scale (34243513875200 : Int) atom0863) (SparsePolynomial.merge (SparsePolynomial.scale (32811347923200 : Int) atom0864) (SparsePolynomial.scale (32256593913600 : Int) atom0865))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (40669074432000 : Int) atom0866) (SparsePolynomial.scale (33480266248800 : Int) atom0867)) (SparsePolynomial.merge (SparsePolynomial.scale (45218805811200 : Int) atom0868) (SparsePolynomial.merge (SparsePolynomial.scale (41305052224800 : Int) atom0869) (SparsePolynomial.scale (46701984016800 : Int) atom0870)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52098915808800 : Int) atom0871) (SparsePolynomial.scale (22544457062400 : Int) atom0872)) (SparsePolynomial.merge (SparsePolynomial.scale (39286802777600 : Int) atom0873) (SparsePolynomial.merge (SparsePolynomial.scale (37104655795200 : Int) atom0874) (SparsePolynomial.scale (35799920755200 : Int) atom0875)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (43481996006400 : Int) atom0876) (SparsePolynomial.scale (35727947136000 : Int) atom0877)) (SparsePolynomial.merge (SparsePolynomial.scale (49377054182400 : Int) atom0878) (SparsePolynomial.merge (SparsePolynomial.scale (42461403264000 : Int) atom0879) (SparsePolynomial.scale (47380775500800 : Int) atom0880)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52300147737600 : Int) atom0881) (SparsePolynomial.scale (22036670566400 : Int) atom0882)) (SparsePolynomial.merge (SparsePolynomial.scale (40545867353600 : Int) atom0883) (SparsePolynomial.merge (SparsePolynomial.scale (38322985433600 : Int) atom0884) (SparsePolynomial.scale (42195811302400 : Int) atom0885))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36822593830400 : Int) atom0886) (SparsePolynomial.scale (49436196275200 : Int) atom0887)) (SparsePolynomial.merge (SparsePolynomial.scale (43193208755200 : Int) atom0888) (SparsePolynomial.merge (SparsePolynomial.scale (47080567475200 : Int) atom0889) (SparsePolynomial.scale (51625627200000 : Int) atom0890)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23512015756800 : Int) atom0891) (SparsePolynomial.scale (42544303142400 : Int) atom0892)) (SparsePolynomial.merge (SparsePolynomial.scale (45194813697600 : Int) atom0893) (SparsePolynomial.merge (SparsePolynomial.scale (38463278328000 : Int) atom0894) (SparsePolynomial.scale (52981496064000 : Int) atom0895)))))))) := by decide +kernel
theorem block012_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block012 := by
  rw [block012_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0816_nonneg g hg hA hB) (atom0817_nonneg g hg hA hB)) (add_nonneg (atom0818_nonneg g hg hA hB) (add_nonneg (atom0819_nonneg g hg hA hB) (atom0820_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0821_nonneg g hg hA hB) (atom0822_nonneg g hg hA hB)) (add_nonneg (atom0823_nonneg g hg hA hB) (add_nonneg (atom0824_nonneg g hg hA hB) (atom0825_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0826_nonneg g hg hA hB) (atom0827_nonneg g hg hA hB)) (add_nonneg (atom0828_nonneg g hg hA hB) (add_nonneg (atom0829_nonneg g hg hA hB) (atom0830_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0831_nonneg g hg hA hB) (atom0832_nonneg g hg hA hB)) (add_nonneg (atom0833_nonneg g hg hA hB) (add_nonneg (atom0834_nonneg g hg hA hB) (atom0835_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0836_nonneg g hg hA hB) (atom0837_nonneg g hg hA hB)) (add_nonneg (atom0838_nonneg g hg hA hB) (add_nonneg (atom0839_nonneg g hg hA hB) (atom0840_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0841_nonneg g hg hA hB) (atom0842_nonneg g hg hA hB)) (add_nonneg (atom0843_nonneg g hg hA hB) (add_nonneg (atom0844_nonneg g hg hA hB) (atom0845_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0846_nonneg g hg hA hB) (atom0847_nonneg g hg hA hB)) (add_nonneg (atom0848_nonneg g hg hA hB) (add_nonneg (atom0849_nonneg g hg hA hB) (atom0850_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0851_nonneg g hg hA hB) (atom0852_nonneg g hg hA hB)) (add_nonneg (atom0853_nonneg g hg hA hB) (add_nonneg (atom0854_nonneg g hg hA hB) (atom0855_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0856_nonneg g hg hA hB) (atom0857_nonneg g hg hA hB)) (add_nonneg (atom0858_nonneg g hg hA hB) (add_nonneg (atom0859_nonneg g hg hA hB) (atom0860_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0861_nonneg g hg hA hB) (atom0862_nonneg g hg hA hB)) (add_nonneg (atom0863_nonneg g hg hA hB) (add_nonneg (atom0864_nonneg g hg hA hB) (atom0865_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0866_nonneg g hg hA hB) (atom0867_nonneg g hg hA hB)) (add_nonneg (atom0868_nonneg g hg hA hB) (add_nonneg (atom0869_nonneg g hg hA hB) (atom0870_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0871_nonneg g hg hA hB) (atom0872_nonneg g hg hA hB)) (add_nonneg (atom0873_nonneg g hg hA hB) (add_nonneg (atom0874_nonneg g hg hA hB) (atom0875_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0876_nonneg g hg hA hB) (atom0877_nonneg g hg hA hB)) (add_nonneg (atom0878_nonneg g hg hA hB) (add_nonneg (atom0879_nonneg g hg hA hB) (atom0880_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0881_nonneg g hg hA hB) (atom0882_nonneg g hg hA hB)) (add_nonneg (atom0883_nonneg g hg hA hB) (add_nonneg (atom0884_nonneg g hg hA hB) (atom0885_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0886_nonneg g hg hA hB) (atom0887_nonneg g hg hA hB)) (add_nonneg (atom0888_nonneg g hg hA hB) (add_nonneg (atom0889_nonneg g hg hA hB) (atom0890_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0891_nonneg g hg hA hB) (atom0892_nonneg g hg hA hB)) (add_nonneg (atom0893_nonneg g hg hA hB) (add_nonneg (atom0894_nonneg g hg hA hB) (atom0895_nonneg g hg hA hB))))))))

end APPT.Finite21
