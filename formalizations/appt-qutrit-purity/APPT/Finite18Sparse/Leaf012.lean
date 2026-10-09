import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0895 : SparsePolynomial.Poly := [([6,16,16], 1)]
theorem eval_atom0895 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182136240 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896 : SparsePolynomial.Poly := [([6,16,17], 1)]
theorem eval_atom0896 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 6) * (g 16) * (g 17)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5136502230 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897 : SparsePolynomial.Poly := [([6,17,17], 1)]
theorem eval_atom0897 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4373859870 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom0898 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154863360 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom0899 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78704640 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900 : SparsePolynomial.Poly := [([7,7,12], 1)]
theorem eval_atom0900 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 7) * (g 7) * (g 12)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155020320 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom0901 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158595840 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902 : SparsePolynomial.Poly := [([7,8,10], 1)]
theorem eval_atom0902 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 7) * (g 8) * (g 10)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903 : SparsePolynomial.Poly := [([7,8,11], 1)]
theorem eval_atom0903 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 7) * (g 8) * (g 11)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904 : SparsePolynomial.Poly := [([7,8,12], 1)]
theorem eval_atom0904 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 7) * (g 8) * (g 12)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87669792 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905 : SparsePolynomial.Poly := [([7,8,15], 1)]
theorem eval_atom0905 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906 : SparsePolynomial.Poly := [([7,8,16], 1)]
theorem eval_atom0906 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 7) * (g 8) * (g 16)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907 : SparsePolynomial.Poly := [([7,8,17], 1)]
theorem eval_atom0907 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom0908 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411045120 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909 : SparsePolynomial.Poly := [([7,9,10], 1)]
theorem eval_atom0909 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (628784640 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910 : SparsePolynomial.Poly := [([7,9,11], 1)]
theorem eval_atom0910 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (786193920 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911 : SparsePolynomial.Poly := [([7,9,12], 1)]
theorem eval_atom0911 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232689600 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912 : SparsePolynomial.Poly := [([7,9,13], 1)]
theorem eval_atom0912 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13607520 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913 : SparsePolynomial.Poly := [([7,9,14], 1)]
theorem eval_atom0913 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (701867040 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914 : SparsePolynomial.Poly := [([7,9,15], 1)]
theorem eval_atom0914 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1929608160 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915 : SparsePolynomial.Poly := [([7,9,16], 1)]
theorem eval_atom0915 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3909670560 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916 : SparsePolynomial.Poly := [([7,9,17], 1)]
theorem eval_atom0916 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6267332160 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom0917 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (891244800 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom0918 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1609136640 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919 : SparsePolynomial.Poly := [([7,10,12], 1)]
theorem eval_atom0919 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1344916800 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920 : SparsePolynomial.Poly := [([7,10,13], 1)]
theorem eval_atom0920 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1404100320 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921 : SparsePolynomial.Poly := [([7,10,14], 1)]
theorem eval_atom0921 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2940756000 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922 : SparsePolynomial.Poly := [([7,10,15], 1)]
theorem eval_atom0922 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 7) * (g 10) * (g 15)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3706055520 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923 : SparsePolynomial.Poly := [([7,10,16], 1)]
theorem eval_atom0923 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 7) * (g 10) * (g 16)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5793806880 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924 : SparsePolynomial.Poly := [([7,10,17], 1)]
theorem eval_atom0924 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 7) * (g 10) * (g 17)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8475644160 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom0925 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1725016320 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926 : SparsePolynomial.Poly := [([7,11,12], 1)]
theorem eval_atom0926 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2334026880 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927 : SparsePolynomial.Poly := [([7,11,13], 1)]
theorem eval_atom0927 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2590296480 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928 : SparsePolynomial.Poly := [([7,11,14], 1)]
theorem eval_atom0928 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4993500960 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0929 : SparsePolynomial.Poly := [([7,11,15], 1)]
theorem eval_atom0929 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 7) * (g 11) * (g 15)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6174312480 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930 : SparsePolynomial.Poly := [([7,11,16], 1)]
theorem eval_atom0930 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 7) * (g 11) * (g 16)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7280074080 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931 : SparsePolynomial.Poly := [([7,11,17], 1)]
theorem eval_atom0931 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 7) * (g 11) * (g 17)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12177524160 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932 : SparsePolynomial.Poly := [([7,12,12], 1)]
theorem eval_atom0932 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2643701760 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933 : SparsePolynomial.Poly := [([7,12,13], 1)]
theorem eval_atom0933 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5717445840 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934 : SparsePolynomial.Poly := [([7,12,14], 1)]
theorem eval_atom0934 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11409847200 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935 : SparsePolynomial.Poly := [([7,12,15], 1)]
theorem eval_atom0935 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 7) * (g 12) * (g 15)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12355259760 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936 : SparsePolynomial.Poly := [([7,12,16], 1)]
theorem eval_atom0936 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 7) * (g 12) * (g 16)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9602218800 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937 : SparsePolynomial.Poly := [([7,12,17], 1)]
theorem eval_atom0937 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 7) * (g 12) * (g 17)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15732480240 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938 : SparsePolynomial.Poly := [([7,13,13], 1)]
theorem eval_atom0938 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2227212288 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939 : SparsePolynomial.Poly := [([7,13,14], 1)]
theorem eval_atom0939 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9005351400 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940 : SparsePolynomial.Poly := [([7,13,15], 1)]
theorem eval_atom0940 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 7) * (g 13) * (g 15)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10554219720 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941 : SparsePolynomial.Poly := [([7,13,16], 1)]
theorem eval_atom0941 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 7) * (g 13) * (g 16)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8388355680 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942 : SparsePolynomial.Poly := [([7,13,17], 1)]
theorem eval_atom0942 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 7) * (g 13) * (g 17)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11756106540 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943 : SparsePolynomial.Poly := [([7,14,14], 1)]
theorem eval_atom0943 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7560675000 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944 : SparsePolynomial.Poly := [([7,14,15], 1)]
theorem eval_atom0944 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 7) * (g 14) * (g 15)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12812030280 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945 : SparsePolynomial.Poly := [([7,14,16], 1)]
theorem eval_atom0945 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 7) * (g 14) * (g 16)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10325020320 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946 : SparsePolynomial.Poly := [([7,14,17], 1)]
theorem eval_atom0946 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 7) * (g 14) * (g 17)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14890848480 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947 : SparsePolynomial.Poly := [([7,15,15], 1)]
theorem eval_atom0947 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3863096280 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948 : SparsePolynomial.Poly := [([7,15,16], 1)]
theorem eval_atom0948 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 7) * (g 15) * (g 16)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6214863960 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949 : SparsePolynomial.Poly := [([7,15,17], 1)]
theorem eval_atom0949 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 7) * (g 15) * (g 17)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11200519260 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950 : SparsePolynomial.Poly := [([7,16,16], 1)]
theorem eval_atom0950 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (928467360 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951 : SparsePolynomial.Poly := [([7,16,17], 1)]
theorem eval_atom0951 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 7) * (g 16) * (g 17)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7244896500 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952 : SparsePolynomial.Poly := [([7,17,17], 1)]
theorem eval_atom0952 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5633486820 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom0953 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114117120 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom0954 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123425280 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955 : SparsePolynomial.Poly := [([8,9,11], 1)]
theorem eval_atom0955 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956 : SparsePolynomial.Poly := [([8,9,13], 1)]
theorem eval_atom0956 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198804480 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom0957 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (697544160 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958 : SparsePolynomial.Poly := [([8,9,15], 1)]
theorem eval_atom0958 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1456949760 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959 : SparsePolynomial.Poly := [([8,9,16], 1)]
theorem eval_atom0959 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 8) * (g 9) * (g 16)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2516290560 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960 : SparsePolynomial.Poly := [([8,9,17], 1)]
theorem eval_atom0960 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3703230720 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom0961 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (446215680 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom0962 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (715852800 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom0963 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34334208 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom0964 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1546800480 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965 : SparsePolynomial.Poly := [([8,10,15], 1)]
theorem eval_atom0965 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1968756480 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966 : SparsePolynomial.Poly := [([8,10,16], 1)]
theorem eval_atom0966 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3971847168 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967 : SparsePolynomial.Poly := [([8,10,17], 1)]
theorem eval_atom0967 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6637222080 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom0968 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1172897280 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom0969 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (947796480 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom0970 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1267307520 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom0971 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3880321440 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972 : SparsePolynomial.Poly := [([8,11,15], 1)]
theorem eval_atom0972 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4842781440 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973 : SparsePolynomial.Poly := [([8,11,16], 1)]
theorem eval_atom0973 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6031779840 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974 : SparsePolynomial.Poly := [([8,11,17], 1)]
theorem eval_atom0974 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11064781440 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block012 : SparsePolynomial.Poly := [([6,16,16], 182136240), ([6,16,17], 5136502230), ([6,17,17], 4373859870), ([7,7,7], 154863360), ([7,7,8], 78704640), ([7,7,12], 155020320), ([7,8,8], 158595840), ([7,8,10], 103864320), ([7,8,11], 207728640), ([7,8,12], 87669792), ([7,8,15], 1180247040), ([7,8,16], 2293143552), ([7,8,17], 3586383360), ([7,9,9], 411045120), ([7,9,10], 628784640), ([7,9,11], 786193920), ([7,9,12], 232689600), ([7,9,13], 13607520), ([7,9,14], 701867040), ([7,9,15], 1929608160), ([7,9,16], 3909670560), ([7,9,17], 6267332160), ([7,10,10], 891244800), ([7,10,11], 1609136640), ([7,10,12], 1344916800), ([7,10,13], 1404100320), ([7,10,14], 2940756000), ([7,10,15], 3706055520), ([7,10,16], 5793806880), ([7,10,17], 8475644160), ([7,11,11], 1725016320), ([7,11,12], 2334026880), ([7,11,13], 2590296480), ([7,11,14], 4993500960), ([7,11,15], 6174312480), ([7,11,16], 7280074080), ([7,11,17], 12177524160), ([7,12,12], 2643701760), ([7,12,13], 5717445840), ([7,12,14], 11409847200), ([7,12,15], 12355259760), ([7,12,16], 9602218800), ([7,12,17], 15732480240), ([7,13,13], 2227212288), ([7,13,14], 9005351400), ([7,13,15], 10554219720), ([7,13,16], 8388355680), ([7,13,17], 11756106540), ([7,14,14], 7560675000), ([7,14,15], 12812030280), ([7,14,16], 10325020320), ([7,14,17], 14890848480), ([7,15,15], 3863096280), ([7,15,16], 6214863960), ([7,15,17], 11200519260), ([7,16,16], 928467360), ([7,16,17], 7244896500), ([7,17,17], 5633486820), ([8,8,8], 114117120), ([8,9,9], 123425280), ([8,9,11], 103864320), ([8,9,13], 198804480), ([8,9,14], 697544160), ([8,9,15], 1456949760), ([8,9,16], 2516290560), ([8,9,17], 3703230720), ([8,10,10], 446215680), ([8,10,11], 715852800), ([8,10,12], 34334208), ([8,10,14], 1546800480), ([8,10,15], 1968756480), ([8,10,16], 3971847168), ([8,10,17], 6637222080), ([8,11,11], 1172897280), ([8,11,12], 947796480), ([8,11,13], 1267307520), ([8,11,14], 3880321440), ([8,11,15], 4842781440), ([8,11,16], 6031779840), ([8,11,17], 11064781440)]
theorem block012_data : block012 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (182136240 : Int) atom0895) (SparsePolynomial.scale (5136502230 : Int) atom0896)) (SparsePolynomial.merge (SparsePolynomial.scale (4373859870 : Int) atom0897) (SparsePolynomial.merge (SparsePolynomial.scale (154863360 : Int) atom0898) (SparsePolynomial.scale (78704640 : Int) atom0899)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (155020320 : Int) atom0900) (SparsePolynomial.scale (158595840 : Int) atom0901)) (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0902) (SparsePolynomial.merge (SparsePolynomial.scale (207728640 : Int) atom0903) (SparsePolynomial.scale (87669792 : Int) atom0904))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1180247040 : Int) atom0905) (SparsePolynomial.scale (2293143552 : Int) atom0906)) (SparsePolynomial.merge (SparsePolynomial.scale (3586383360 : Int) atom0907) (SparsePolynomial.merge (SparsePolynomial.scale (411045120 : Int) atom0908) (SparsePolynomial.scale (628784640 : Int) atom0909)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (786193920 : Int) atom0910) (SparsePolynomial.scale (232689600 : Int) atom0911)) (SparsePolynomial.merge (SparsePolynomial.scale (13607520 : Int) atom0912) (SparsePolynomial.merge (SparsePolynomial.scale (701867040 : Int) atom0913) (SparsePolynomial.scale (1929608160 : Int) atom0914)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3909670560 : Int) atom0915) (SparsePolynomial.scale (6267332160 : Int) atom0916)) (SparsePolynomial.merge (SparsePolynomial.scale (891244800 : Int) atom0917) (SparsePolynomial.merge (SparsePolynomial.scale (1609136640 : Int) atom0918) (SparsePolynomial.scale (1344916800 : Int) atom0919)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1404100320 : Int) atom0920) (SparsePolynomial.scale (2940756000 : Int) atom0921)) (SparsePolynomial.merge (SparsePolynomial.scale (3706055520 : Int) atom0922) (SparsePolynomial.merge (SparsePolynomial.scale (5793806880 : Int) atom0923) (SparsePolynomial.scale (8475644160 : Int) atom0924))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1725016320 : Int) atom0925) (SparsePolynomial.scale (2334026880 : Int) atom0926)) (SparsePolynomial.merge (SparsePolynomial.scale (2590296480 : Int) atom0927) (SparsePolynomial.merge (SparsePolynomial.scale (4993500960 : Int) atom0928) (SparsePolynomial.scale (6174312480 : Int) atom0929)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7280074080 : Int) atom0930) (SparsePolynomial.scale (12177524160 : Int) atom0931)) (SparsePolynomial.merge (SparsePolynomial.scale (2643701760 : Int) atom0932) (SparsePolynomial.merge (SparsePolynomial.scale (5717445840 : Int) atom0933) (SparsePolynomial.scale (11409847200 : Int) atom0934))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12355259760 : Int) atom0935) (SparsePolynomial.scale (9602218800 : Int) atom0936)) (SparsePolynomial.merge (SparsePolynomial.scale (15732480240 : Int) atom0937) (SparsePolynomial.merge (SparsePolynomial.scale (2227212288 : Int) atom0938) (SparsePolynomial.scale (9005351400 : Int) atom0939)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10554219720 : Int) atom0940) (SparsePolynomial.scale (8388355680 : Int) atom0941)) (SparsePolynomial.merge (SparsePolynomial.scale (11756106540 : Int) atom0942) (SparsePolynomial.merge (SparsePolynomial.scale (7560675000 : Int) atom0943) (SparsePolynomial.scale (12812030280 : Int) atom0944))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10325020320 : Int) atom0945) (SparsePolynomial.scale (14890848480 : Int) atom0946)) (SparsePolynomial.merge (SparsePolynomial.scale (3863096280 : Int) atom0947) (SparsePolynomial.merge (SparsePolynomial.scale (6214863960 : Int) atom0948) (SparsePolynomial.scale (11200519260 : Int) atom0949)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (928467360 : Int) atom0950) (SparsePolynomial.scale (7244896500 : Int) atom0951)) (SparsePolynomial.merge (SparsePolynomial.scale (5633486820 : Int) atom0952) (SparsePolynomial.merge (SparsePolynomial.scale (114117120 : Int) atom0953) (SparsePolynomial.scale (123425280 : Int) atom0954)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (103864320 : Int) atom0955) (SparsePolynomial.scale (198804480 : Int) atom0956)) (SparsePolynomial.merge (SparsePolynomial.scale (697544160 : Int) atom0957) (SparsePolynomial.merge (SparsePolynomial.scale (1456949760 : Int) atom0958) (SparsePolynomial.scale (2516290560 : Int) atom0959)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3703230720 : Int) atom0960) (SparsePolynomial.scale (446215680 : Int) atom0961)) (SparsePolynomial.merge (SparsePolynomial.scale (715852800 : Int) atom0962) (SparsePolynomial.merge (SparsePolynomial.scale (34334208 : Int) atom0963) (SparsePolynomial.scale (1546800480 : Int) atom0964))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1968756480 : Int) atom0965) (SparsePolynomial.scale (3971847168 : Int) atom0966)) (SparsePolynomial.merge (SparsePolynomial.scale (6637222080 : Int) atom0967) (SparsePolynomial.merge (SparsePolynomial.scale (1172897280 : Int) atom0968) (SparsePolynomial.scale (947796480 : Int) atom0969)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1267307520 : Int) atom0970) (SparsePolynomial.scale (3880321440 : Int) atom0971)) (SparsePolynomial.merge (SparsePolynomial.scale (4842781440 : Int) atom0972) (SparsePolynomial.merge (SparsePolynomial.scale (6031779840 : Int) atom0973) (SparsePolynomial.scale (11064781440 : Int) atom0974)))))))) := by decide +kernel
theorem block012_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block012 := by
  rw [block012_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0895_nonneg g hg hA hB) (atom0896_nonneg g hg hA hB)) (add_nonneg (atom0897_nonneg g hg hA hB) (add_nonneg (atom0898_nonneg g hg hA hB) (atom0899_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0900_nonneg g hg hA hB) (atom0901_nonneg g hg hA hB)) (add_nonneg (atom0902_nonneg g hg hA hB) (add_nonneg (atom0903_nonneg g hg hA hB) (atom0904_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0905_nonneg g hg hA hB) (atom0906_nonneg g hg hA hB)) (add_nonneg (atom0907_nonneg g hg hA hB) (add_nonneg (atom0908_nonneg g hg hA hB) (atom0909_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0910_nonneg g hg hA hB) (atom0911_nonneg g hg hA hB)) (add_nonneg (atom0912_nonneg g hg hA hB) (add_nonneg (atom0913_nonneg g hg hA hB) (atom0914_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0915_nonneg g hg hA hB) (atom0916_nonneg g hg hA hB)) (add_nonneg (atom0917_nonneg g hg hA hB) (add_nonneg (atom0918_nonneg g hg hA hB) (atom0919_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0920_nonneg g hg hA hB) (atom0921_nonneg g hg hA hB)) (add_nonneg (atom0922_nonneg g hg hA hB) (add_nonneg (atom0923_nonneg g hg hA hB) (atom0924_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0925_nonneg g hg hA hB) (atom0926_nonneg g hg hA hB)) (add_nonneg (atom0927_nonneg g hg hA hB) (add_nonneg (atom0928_nonneg g hg hA hB) (atom0929_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0930_nonneg g hg hA hB) (atom0931_nonneg g hg hA hB)) (add_nonneg (atom0932_nonneg g hg hA hB) (add_nonneg (atom0933_nonneg g hg hA hB) (atom0934_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0935_nonneg g hg hA hB) (atom0936_nonneg g hg hA hB)) (add_nonneg (atom0937_nonneg g hg hA hB) (add_nonneg (atom0938_nonneg g hg hA hB) (atom0939_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0940_nonneg g hg hA hB) (atom0941_nonneg g hg hA hB)) (add_nonneg (atom0942_nonneg g hg hA hB) (add_nonneg (atom0943_nonneg g hg hA hB) (atom0944_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0945_nonneg g hg hA hB) (atom0946_nonneg g hg hA hB)) (add_nonneg (atom0947_nonneg g hg hA hB) (add_nonneg (atom0948_nonneg g hg hA hB) (atom0949_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0950_nonneg g hg hA hB) (atom0951_nonneg g hg hA hB)) (add_nonneg (atom0952_nonneg g hg hA hB) (add_nonneg (atom0953_nonneg g hg hA hB) (atom0954_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0955_nonneg g hg hA hB) (atom0956_nonneg g hg hA hB)) (add_nonneg (atom0957_nonneg g hg hA hB) (add_nonneg (atom0958_nonneg g hg hA hB) (atom0959_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0960_nonneg g hg hA hB) (atom0961_nonneg g hg hA hB)) (add_nonneg (atom0962_nonneg g hg hA hB) (add_nonneg (atom0963_nonneg g hg hA hB) (atom0964_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0965_nonneg g hg hA hB) (atom0966_nonneg g hg hA hB)) (add_nonneg (atom0967_nonneg g hg hA hB) (add_nonneg (atom0968_nonneg g hg hA hB) (atom0969_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0970_nonneg g hg hA hB) (atom0971_nonneg g hg hA hB)) (add_nonneg (atom0972_nonneg g hg hA hB) (add_nonneg (atom0973_nonneg g hg hA hB) (atom0974_nonneg g hg hA hB))))))))

end APPT.Finite18
