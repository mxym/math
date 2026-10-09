import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0815 : SparsePolynomial.Poly := [([5,12,15], 1)]
theorem eval_atom0815 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0815 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0815_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13013137800 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0816 : SparsePolynomial.Poly := [([5,12,16], 1)]
theorem eval_atom0816 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0816 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom0816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0816_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9515050920 : Int) atom0816) := by
  rw [SparsePolynomial.eval_scale, eval_atom0816]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0817 : SparsePolynomial.Poly := [([5,12,17], 1)]
theorem eval_atom0817 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0817 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom0817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0817_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14900266440 : Int) atom0817) := by
  rw [SparsePolynomial.eval_scale, eval_atom0817]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0818 : SparsePolynomial.Poly := [([5,13,13], 1)]
theorem eval_atom0818 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0818 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom0818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0818_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3202633728 : Int) atom0818) := by
  rw [SparsePolynomial.eval_scale, eval_atom0818]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0819 : SparsePolynomial.Poly := [([5,13,14], 1)]
theorem eval_atom0819 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0819 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom0819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0819_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10330996320 : Int) atom0819) := by
  rw [SparsePolynomial.eval_scale, eval_atom0819]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0820 : SparsePolynomial.Poly := [([5,13,15], 1)]
theorem eval_atom0820 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0820 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom0820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0820_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11120842620 : Int) atom0820) := by
  rw [SparsePolynomial.eval_scale, eval_atom0820]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0821 : SparsePolynomial.Poly := [([5,13,16], 1)]
theorem eval_atom0821 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0821 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom0821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0821_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8447358000 : Int) atom0821) := by
  rw [SparsePolynomial.eval_scale, eval_atom0821]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0822 : SparsePolynomial.Poly := [([5,13,17], 1)]
theorem eval_atom0822 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0822 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom0822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0822_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10737773370 : Int) atom0822) := by
  rw [SparsePolynomial.eval_scale, eval_atom0822]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0823 : SparsePolynomial.Poly := [([5,14,14], 1)]
theorem eval_atom0823 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0823 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom0823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0823_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7850979000 : Int) atom0823) := by
  rw [SparsePolynomial.eval_scale, eval_atom0823]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0824 : SparsePolynomial.Poly := [([5,14,15], 1)]
theorem eval_atom0824 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0824 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom0824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0824_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12484453680 : Int) atom0824) := by
  rw [SparsePolynomial.eval_scale, eval_atom0824]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0825 : SparsePolynomial.Poly := [([5,14,16], 1)]
theorem eval_atom0825 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0825 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom0825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0825_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9208198920 : Int) atom0825) := by
  rw [SparsePolynomial.eval_scale, eval_atom0825]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0826 : SparsePolynomial.Poly := [([5,14,17], 1)]
theorem eval_atom0826 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0826 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom0826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0826_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12481979400 : Int) atom0826) := by
  rw [SparsePolynomial.eval_scale, eval_atom0826]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0827 : SparsePolynomial.Poly := [([5,15,15], 1)]
theorem eval_atom0827 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0827 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom0827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0827_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3495594420 : Int) atom0827) := by
  rw [SparsePolynomial.eval_scale, eval_atom0827]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0828 : SparsePolynomial.Poly := [([5,15,16], 1)]
theorem eval_atom0828 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0828 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom0828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0828_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4734746820 : Int) atom0828) := by
  rw [SparsePolynomial.eval_scale, eval_atom0828]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0829 : SparsePolynomial.Poly := [([5,15,17], 1)]
theorem eval_atom0829 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0829 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom0829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0829_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8199759330 : Int) atom0829) := by
  rw [SparsePolynomial.eval_scale, eval_atom0829]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0830 : SparsePolynomial.Poly := [([5,16,17], 1)]
theorem eval_atom0830 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0830 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom0830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0830_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3354207030 : Int) atom0830) := by
  rw [SparsePolynomial.eval_scale, eval_atom0830]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0831 : SparsePolynomial.Poly := [([5,17,17], 1)]
theorem eval_atom0831 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0831 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom0831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0831_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3244305150 : Int) atom0831) := by
  rw [SparsePolynomial.eval_scale, eval_atom0831]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0832 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom0832 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0832 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom0832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0832_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199002240 : Int) atom0832) := by
  rw [SparsePolynomial.eval_scale, eval_atom0832]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0833 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom0833 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0833 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom0833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0833_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0833) := by
  rw [SparsePolynomial.eval_scale, eval_atom0833]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0834 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom0834 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0834 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom0834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0834_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25159680 : Int) atom0834) := by
  rw [SparsePolynomial.eval_scale, eval_atom0834]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0835 : SparsePolynomial.Poly := [([6,6,12], 1)]
theorem eval_atom0835 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0835 = ((g 6) * (g 6) * (g 12)) := by
  norm_num [atom0835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0835_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382258800 : Int) atom0835) := by
  rw [SparsePolynomial.eval_scale, eval_atom0835]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0836 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom0836 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0836 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0836_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180362880 : Int) atom0836) := by
  rw [SparsePolynomial.eval_scale, eval_atom0836]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0837 : SparsePolynomial.Poly := [([6,7,10], 1)]
theorem eval_atom0837 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0837 = ((g 6) * (g 7) * (g 10)) := by
  norm_num [atom0837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0837_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0837) := by
  rw [SparsePolynomial.eval_scale, eval_atom0837]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0838 : SparsePolynomial.Poly := [([6,7,11], 1)]
theorem eval_atom0838 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0838 = ((g 6) * (g 7) * (g 11)) := by
  norm_num [atom0838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0838_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0838) := by
  rw [SparsePolynomial.eval_scale, eval_atom0838]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0839 : SparsePolynomial.Poly := [([6,7,12], 1)]
theorem eval_atom0839 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0839 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom0839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0839_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (469928592 : Int) atom0839) := by
  rw [SparsePolynomial.eval_scale, eval_atom0839]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0840 : SparsePolynomial.Poly := [([6,7,15], 1)]
theorem eval_atom0840 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0840 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom0840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0840_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0840) := by
  rw [SparsePolynomial.eval_scale, eval_atom0840]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0841 : SparsePolynomial.Poly := [([6,7,16], 1)]
theorem eval_atom0841 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0841 = ((g 6) * (g 7) * (g 16)) := by
  norm_num [atom0841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0841_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0841) := by
  rw [SparsePolynomial.eval_scale, eval_atom0841]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0842 : SparsePolynomial.Poly := [([6,7,17], 1)]
theorem eval_atom0842 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0842 = ((g 6) * (g 7) * (g 17)) := by
  norm_num [atom0842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0842_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0842) := by
  rw [SparsePolynomial.eval_scale, eval_atom0842]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0843 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom0843 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0843 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0843_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389278080 : Int) atom0843) := by
  rw [SparsePolynomial.eval_scale, eval_atom0843]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0844 : SparsePolynomial.Poly := [([6,8,9], 1)]
theorem eval_atom0844 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0844 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom0844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0844_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (568454400 : Int) atom0844) := by
  rw [SparsePolynomial.eval_scale, eval_atom0844]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0845 : SparsePolynomial.Poly := [([6,8,10], 1)]
theorem eval_atom0845 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0845 = ((g 6) * (g 8) * (g 10)) := by
  norm_num [atom0845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0845_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (725863680 : Int) atom0845) := by
  rw [SparsePolynomial.eval_scale, eval_atom0845]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0846 : SparsePolynomial.Poly := [([6,8,11], 1)]
theorem eval_atom0846 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0846 = ((g 6) * (g 8) * (g 11)) := by
  norm_num [atom0846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0846_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (883272960 : Int) atom0846) := by
  rw [SparsePolynomial.eval_scale, eval_atom0846]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0847 : SparsePolynomial.Poly := [([6,8,12], 1)]
theorem eval_atom0847 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0847 = ((g 6) * (g 8) * (g 12)) := by
  norm_num [atom0847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0847_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (757621440 : Int) atom0847) := by
  rw [SparsePolynomial.eval_scale, eval_atom0847]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0848 : SparsePolynomial.Poly := [([6,8,13], 1)]
theorem eval_atom0848 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0848 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom0848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0848_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428863920 : Int) atom0848) := by
  rw [SparsePolynomial.eval_scale, eval_atom0848]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849 : SparsePolynomial.Poly := [([6,8,14], 1)]
theorem eval_atom0849 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (816511200 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850 : SparsePolynomial.Poly := [([6,8,15], 1)]
theorem eval_atom0850 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2272055280 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851 : SparsePolynomial.Poly := [([6,8,16], 1)]
theorem eval_atom0851 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4061745360 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852 : SparsePolynomial.Poly := [([6,8,17], 1)]
theorem eval_atom0852 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6158118240 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom0853 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (852681600 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854 : SparsePolynomial.Poly := [([6,9,10], 1)]
theorem eval_atom0854 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1515283200 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855 : SparsePolynomial.Poly := [([6,9,11], 1)]
theorem eval_atom0855 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1675918080 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856 : SparsePolynomial.Poly := [([6,9,12], 1)]
theorem eval_atom0856 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1750199040 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857 : SparsePolynomial.Poly := [([6,9,13], 1)]
theorem eval_atom0857 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1645188720 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858 : SparsePolynomial.Poly := [([6,9,14], 1)]
theorem eval_atom0858 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2642200800 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859 : SparsePolynomial.Poly := [([6,9,15], 1)]
theorem eval_atom0859 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 6) * (g 9) * (g 15)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3897057840 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860 : SparsePolynomial.Poly := [([6,9,16], 1)]
theorem eval_atom0860 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 6) * (g 9) * (g 16)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5871678480 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861 : SparsePolynomial.Poly := [([6,9,17], 1)]
theorem eval_atom0861 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 6) * (g 9) * (g 17)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8109758880 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom0862 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1439971200 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863 : SparsePolynomial.Poly := [([6,10,11], 1)]
theorem eval_atom0863 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2659495680 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864 : SparsePolynomial.Poly := [([6,10,12], 1)]
theorem eval_atom0864 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2848556160 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865 : SparsePolynomial.Poly := [([6,10,13], 1)]
theorem eval_atom0865 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2847306480 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866 : SparsePolynomial.Poly := [([6,10,14], 1)]
theorem eval_atom0866 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4518209760 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867 : SparsePolynomial.Poly := [([6,10,15], 1)]
theorem eval_atom0867 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 6) * (g 10) * (g 15)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5198213040 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868 : SparsePolynomial.Poly := [([6,10,16], 1)]
theorem eval_atom0868 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 6) * (g 10) * (g 16)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7168110480 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869 : SparsePolynomial.Poly := [([6,10,17], 1)]
theorem eval_atom0869 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 6) * (g 10) * (g 17)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9649000800 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom0870 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2330513280 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871 : SparsePolynomial.Poly := [([6,11,12], 1)]
theorem eval_atom0871 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3823796160 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872 : SparsePolynomial.Poly := [([6,11,13], 1)]
theorem eval_atom0872 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3845127600 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873 : SparsePolynomial.Poly := [([6,11,14], 1)]
theorem eval_atom0873 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6208074720 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874 : SparsePolynomial.Poly := [([6,11,15], 1)]
theorem eval_atom0874 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 6) * (g 11) * (g 15)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7191177840 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875 : SparsePolynomial.Poly := [([6,11,16], 1)]
theorem eval_atom0875 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 6) * (g 11) * (g 16)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8066673360 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876 : SparsePolynomial.Poly := [([6,11,17], 1)]
theorem eval_atom0876 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 6) * (g 11) * (g 17)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12681810720 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877 : SparsePolynomial.Poly := [([6,12,12], 1)]
theorem eval_atom0877 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3423651840 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878 : SparsePolynomial.Poly := [([6,12,13], 1)]
theorem eval_atom0878 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6832572120 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879 : SparsePolynomial.Poly := [([6,12,14], 1)]
theorem eval_atom0879 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12177540000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880 : SparsePolynomial.Poly := [([6,12,15], 1)]
theorem eval_atom0880 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 6) * (g 12) * (g 15)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12748840200 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881 : SparsePolynomial.Poly := [([6,12,16], 1)]
theorem eval_atom0881 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 6) * (g 12) * (g 16)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9605408040 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882 : SparsePolynomial.Poly := [([6,12,17], 1)]
theorem eval_atom0882 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 6) * (g 12) * (g 17)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15345278280 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883 : SparsePolynomial.Poly := [([6,13,13], 1)]
theorem eval_atom0883 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2714923008 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884 : SparsePolynomial.Poly := [([6,13,14], 1)]
theorem eval_atom0884 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9583020000 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885 : SparsePolynomial.Poly := [([6,13,15], 1)]
theorem eval_atom0885 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 6) * (g 13) * (g 15)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10709800380 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886 : SparsePolynomial.Poly := [([6,13,16], 1)]
theorem eval_atom0886 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 6) * (g 13) * (g 16)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8121848400 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887 : SparsePolynomial.Poly := [([6,13,17], 1)]
theorem eval_atom0887 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 6) * (g 13) * (g 17)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11055343770 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888 : SparsePolynomial.Poly := [([6,14,14], 1)]
theorem eval_atom0888 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7705827000 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889 : SparsePolynomial.Poly := [([6,14,15], 1)]
theorem eval_atom0889 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 6) * (g 14) * (g 15)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12583600560 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890 : SparsePolynomial.Poly := [([6,14,16], 1)]
theorem eval_atom0890 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 6) * (g 14) * (g 16)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9594135720 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891 : SparsePolynomial.Poly := [([6,14,17], 1)]
theorem eval_atom0891 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 6) * (g 14) * (g 17)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13657509000 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892 : SparsePolynomial.Poly := [([6,15,15], 1)]
theorem eval_atom0892 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3582383220 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893 : SparsePolynomial.Poly := [([6,15,16], 1)]
theorem eval_atom0893 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 6) * (g 15) * (g 16)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5086811700 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894 : SparsePolynomial.Poly := [([6,15,17], 1)]
theorem eval_atom0894 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 6) * (g 15) * (g 17)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9511338690 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block011 : SparsePolynomial.Poly := [([5,12,15], 13013137800), ([5,12,16], 9515050920), ([5,12,17], 14900266440), ([5,13,13], 3202633728), ([5,13,14], 10330996320), ([5,13,15], 11120842620), ([5,13,16], 8447358000), ([5,13,17], 10737773370), ([5,14,14], 7850979000), ([5,14,15], 12484453680), ([5,14,16], 9208198920), ([5,14,17], 12481979400), ([5,15,15], 3495594420), ([5,15,16], 4734746820), ([5,15,17], 8199759330), ([5,16,17], 3354207030), ([5,17,17], 3244305150), ([6,6,6], 199002240), ([6,6,7], 103864320), ([6,6,8], 25159680), ([6,6,12], 382258800), ([6,7,7], 180362880), ([6,7,10], 103864320), ([6,7,11], 207728640), ([6,7,12], 469928592), ([6,7,15], 1180247040), ([6,7,16], 2293143552), ([6,7,17], 3586383360), ([6,8,8], 389278080), ([6,8,9], 568454400), ([6,8,10], 725863680), ([6,8,11], 883272960), ([6,8,12], 757621440), ([6,8,13], 428863920), ([6,8,14], 816511200), ([6,8,15], 2272055280), ([6,8,16], 4061745360), ([6,8,17], 6158118240), ([6,9,9], 852681600), ([6,9,10], 1515283200), ([6,9,11], 1675918080), ([6,9,12], 1750199040), ([6,9,13], 1645188720), ([6,9,14], 2642200800), ([6,9,15], 3897057840), ([6,9,16], 5871678480), ([6,9,17], 8109758880), ([6,10,10], 1439971200), ([6,10,11], 2659495680), ([6,10,12], 2848556160), ([6,10,13], 2847306480), ([6,10,14], 4518209760), ([6,10,15], 5198213040), ([6,10,16], 7168110480), ([6,10,17], 9649000800), ([6,11,11], 2330513280), ([6,11,12], 3823796160), ([6,11,13], 3845127600), ([6,11,14], 6208074720), ([6,11,15], 7191177840), ([6,11,16], 8066673360), ([6,11,17], 12681810720), ([6,12,12], 3423651840), ([6,12,13], 6832572120), ([6,12,14], 12177540000), ([6,12,15], 12748840200), ([6,12,16], 9605408040), ([6,12,17], 15345278280), ([6,13,13], 2714923008), ([6,13,14], 9583020000), ([6,13,15], 10709800380), ([6,13,16], 8121848400), ([6,13,17], 11055343770), ([6,14,14], 7705827000), ([6,14,15], 12583600560), ([6,14,16], 9594135720), ([6,14,17], 13657509000), ([6,15,15], 3582383220), ([6,15,16], 5086811700), ([6,15,17], 9511338690)]
theorem block011_data : block011 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13013137800 : Int) atom0815) (SparsePolynomial.scale (9515050920 : Int) atom0816)) (SparsePolynomial.merge (SparsePolynomial.scale (14900266440 : Int) atom0817) (SparsePolynomial.merge (SparsePolynomial.scale (3202633728 : Int) atom0818) (SparsePolynomial.scale (10330996320 : Int) atom0819)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11120842620 : Int) atom0820) (SparsePolynomial.scale (8447358000 : Int) atom0821)) (SparsePolynomial.merge (SparsePolynomial.scale (10737773370 : Int) atom0822) (SparsePolynomial.merge (SparsePolynomial.scale (7850979000 : Int) atom0823) (SparsePolynomial.scale (12484453680 : Int) atom0824))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9208198920 : Int) atom0825) (SparsePolynomial.scale (12481979400 : Int) atom0826)) (SparsePolynomial.merge (SparsePolynomial.scale (3495594420 : Int) atom0827) (SparsePolynomial.merge (SparsePolynomial.scale (4734746820 : Int) atom0828) (SparsePolynomial.scale (8199759330 : Int) atom0829)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3354207030 : Int) atom0830) (SparsePolynomial.scale (3244305150 : Int) atom0831)) (SparsePolynomial.merge (SparsePolynomial.scale (199002240 : Int) atom0832) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0833) (SparsePolynomial.scale (25159680 : Int) atom0834)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (382258800 : Int) atom0835) (SparsePolynomial.scale (180362880 : Int) atom0836)) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0837) (SparsePolynomial.merge (SparsePolynomial.scale (207728640 : Int) atom0838) (SparsePolynomial.scale (469928592 : Int) atom0839)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1180247040 : Int) atom0840) (SparsePolynomial.scale (2293143552 : Int) atom0841)) (SparsePolynomial.merge (SparsePolynomial.scale (3586383360 : Int) atom0842) (SparsePolynomial.merge (SparsePolynomial.scale (389278080 : Int) atom0843) (SparsePolynomial.scale (568454400 : Int) atom0844))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (725863680 : Int) atom0845) (SparsePolynomial.scale (883272960 : Int) atom0846)) (SparsePolynomial.merge (SparsePolynomial.scale (757621440 : Int) atom0847) (SparsePolynomial.merge (SparsePolynomial.scale (428863920 : Int) atom0848) (SparsePolynomial.scale (816511200 : Int) atom0849)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2272055280 : Int) atom0850) (SparsePolynomial.scale (4061745360 : Int) atom0851)) (SparsePolynomial.merge (SparsePolynomial.scale (6158118240 : Int) atom0852) (SparsePolynomial.merge (SparsePolynomial.scale (852681600 : Int) atom0853) (SparsePolynomial.scale (1515283200 : Int) atom0854))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1675918080 : Int) atom0855) (SparsePolynomial.scale (1750199040 : Int) atom0856)) (SparsePolynomial.merge (SparsePolynomial.scale (1645188720 : Int) atom0857) (SparsePolynomial.merge (SparsePolynomial.scale (2642200800 : Int) atom0858) (SparsePolynomial.scale (3897057840 : Int) atom0859)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5871678480 : Int) atom0860) (SparsePolynomial.scale (8109758880 : Int) atom0861)) (SparsePolynomial.merge (SparsePolynomial.scale (1439971200 : Int) atom0862) (SparsePolynomial.merge (SparsePolynomial.scale (2659495680 : Int) atom0863) (SparsePolynomial.scale (2848556160 : Int) atom0864))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2847306480 : Int) atom0865) (SparsePolynomial.scale (4518209760 : Int) atom0866)) (SparsePolynomial.merge (SparsePolynomial.scale (5198213040 : Int) atom0867) (SparsePolynomial.merge (SparsePolynomial.scale (7168110480 : Int) atom0868) (SparsePolynomial.scale (9649000800 : Int) atom0869)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2330513280 : Int) atom0870) (SparsePolynomial.scale (3823796160 : Int) atom0871)) (SparsePolynomial.merge (SparsePolynomial.scale (3845127600 : Int) atom0872) (SparsePolynomial.merge (SparsePolynomial.scale (6208074720 : Int) atom0873) (SparsePolynomial.scale (7191177840 : Int) atom0874)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8066673360 : Int) atom0875) (SparsePolynomial.scale (12681810720 : Int) atom0876)) (SparsePolynomial.merge (SparsePolynomial.scale (3423651840 : Int) atom0877) (SparsePolynomial.merge (SparsePolynomial.scale (6832572120 : Int) atom0878) (SparsePolynomial.scale (12177540000 : Int) atom0879)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12748840200 : Int) atom0880) (SparsePolynomial.scale (9605408040 : Int) atom0881)) (SparsePolynomial.merge (SparsePolynomial.scale (15345278280 : Int) atom0882) (SparsePolynomial.merge (SparsePolynomial.scale (2714923008 : Int) atom0883) (SparsePolynomial.scale (9583020000 : Int) atom0884))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10709800380 : Int) atom0885) (SparsePolynomial.scale (8121848400 : Int) atom0886)) (SparsePolynomial.merge (SparsePolynomial.scale (11055343770 : Int) atom0887) (SparsePolynomial.merge (SparsePolynomial.scale (7705827000 : Int) atom0888) (SparsePolynomial.scale (12583600560 : Int) atom0889)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9594135720 : Int) atom0890) (SparsePolynomial.scale (13657509000 : Int) atom0891)) (SparsePolynomial.merge (SparsePolynomial.scale (3582383220 : Int) atom0892) (SparsePolynomial.merge (SparsePolynomial.scale (5086811700 : Int) atom0893) (SparsePolynomial.scale (9511338690 : Int) atom0894)))))))) := by decide +kernel
theorem block011_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block011 := by
  rw [block011_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0815_nonneg g hg hA hB) (atom0816_nonneg g hg hA hB)) (add_nonneg (atom0817_nonneg g hg hA hB) (add_nonneg (atom0818_nonneg g hg hA hB) (atom0819_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0820_nonneg g hg hA hB) (atom0821_nonneg g hg hA hB)) (add_nonneg (atom0822_nonneg g hg hA hB) (add_nonneg (atom0823_nonneg g hg hA hB) (atom0824_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0825_nonneg g hg hA hB) (atom0826_nonneg g hg hA hB)) (add_nonneg (atom0827_nonneg g hg hA hB) (add_nonneg (atom0828_nonneg g hg hA hB) (atom0829_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0830_nonneg g hg hA hB) (atom0831_nonneg g hg hA hB)) (add_nonneg (atom0832_nonneg g hg hA hB) (add_nonneg (atom0833_nonneg g hg hA hB) (atom0834_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0835_nonneg g hg hA hB) (atom0836_nonneg g hg hA hB)) (add_nonneg (atom0837_nonneg g hg hA hB) (add_nonneg (atom0838_nonneg g hg hA hB) (atom0839_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0840_nonneg g hg hA hB) (atom0841_nonneg g hg hA hB)) (add_nonneg (atom0842_nonneg g hg hA hB) (add_nonneg (atom0843_nonneg g hg hA hB) (atom0844_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0845_nonneg g hg hA hB) (atom0846_nonneg g hg hA hB)) (add_nonneg (atom0847_nonneg g hg hA hB) (add_nonneg (atom0848_nonneg g hg hA hB) (atom0849_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0850_nonneg g hg hA hB) (atom0851_nonneg g hg hA hB)) (add_nonneg (atom0852_nonneg g hg hA hB) (add_nonneg (atom0853_nonneg g hg hA hB) (atom0854_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0855_nonneg g hg hA hB) (atom0856_nonneg g hg hA hB)) (add_nonneg (atom0857_nonneg g hg hA hB) (add_nonneg (atom0858_nonneg g hg hA hB) (atom0859_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0860_nonneg g hg hA hB) (atom0861_nonneg g hg hA hB)) (add_nonneg (atom0862_nonneg g hg hA hB) (add_nonneg (atom0863_nonneg g hg hA hB) (atom0864_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0865_nonneg g hg hA hB) (atom0866_nonneg g hg hA hB)) (add_nonneg (atom0867_nonneg g hg hA hB) (add_nonneg (atom0868_nonneg g hg hA hB) (atom0869_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0870_nonneg g hg hA hB) (atom0871_nonneg g hg hA hB)) (add_nonneg (atom0872_nonneg g hg hA hB) (add_nonneg (atom0873_nonneg g hg hA hB) (atom0874_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0875_nonneg g hg hA hB) (atom0876_nonneg g hg hA hB)) (add_nonneg (atom0877_nonneg g hg hA hB) (add_nonneg (atom0878_nonneg g hg hA hB) (atom0879_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0880_nonneg g hg hA hB) (atom0881_nonneg g hg hA hB)) (add_nonneg (atom0882_nonneg g hg hA hB) (add_nonneg (atom0883_nonneg g hg hA hB) (atom0884_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0885_nonneg g hg hA hB) (atom0886_nonneg g hg hA hB)) (add_nonneg (atom0887_nonneg g hg hA hB) (add_nonneg (atom0888_nonneg g hg hA hB) (atom0889_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0890_nonneg g hg hA hB) (atom0891_nonneg g hg hA hB)) (add_nonneg (atom0892_nonneg g hg hA hB) (add_nonneg (atom0893_nonneg g hg hA hB) (atom0894_nonneg g hg hA hB))))))))

end APPT.Finite18
