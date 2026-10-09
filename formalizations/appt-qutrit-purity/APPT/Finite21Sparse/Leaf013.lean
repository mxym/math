import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0896 : SparsePolynomial.Poly := [([3,13,18], 1)]
theorem eval_atom0896 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 3) * (g 13) * (g 18)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47411171942400 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897 : SparsePolynomial.Poly := [([3,13,19], 1)]
theorem eval_atom0897 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 3) * (g 13) * (g 19)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44102287944000 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898 : SparsePolynomial.Poly := [([3,13,20], 1)]
theorem eval_atom0898 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 3) * (g 13) * (g 20)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53975438899200 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899 : SparsePolynomial.Poly := [([3,14,14], 1)]
theorem eval_atom0899 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26303458406400 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900 : SparsePolynomial.Poly := [([3,14,15], 1)]
theorem eval_atom0900 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48520679961600 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901 : SparsePolynomial.Poly := [([3,14,16], 1)]
theorem eval_atom0901 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39984813388800 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902 : SparsePolynomial.Poly := [([3,14,17], 1)]
theorem eval_atom0902 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58281619737600 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903 : SparsePolynomial.Poly := [([3,14,18], 1)]
theorem eval_atom0903 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 3) * (g 14) * (g 18)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53383959014400 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904 : SparsePolynomial.Poly := [([3,14,19], 1)]
theorem eval_atom0904 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 3) * (g 14) * (g 19)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44697323059200 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905 : SparsePolynomial.Poly := [([3,14,20], 1)]
theorem eval_atom0905 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 3) * (g 14) * (g 20)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59921164800000 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906 : SparsePolynomial.Poly := [([3,15,15], 1)]
theorem eval_atom0906 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30559794048000 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907 : SparsePolynomial.Poly := [([3,15,16], 1)]
theorem eval_atom0907 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52085022796800 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908 : SparsePolynomial.Poly := [([3,15,17], 1)]
theorem eval_atom0908 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72395953459200 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909 : SparsePolynomial.Poly := [([3,15,18], 1)]
theorem eval_atom0909 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 3) * (g 15) * (g 18)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66129770649600 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910 : SparsePolynomial.Poly := [([3,15,19], 1)]
theorem eval_atom0910 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 3) * (g 15) * (g 19)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43317203328000 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911 : SparsePolynomial.Poly := [([3,15,20], 1)]
theorem eval_atom0911 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 3) * (g 15) * (g 20)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63125980646400 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912 : SparsePolynomial.Poly := [([3,16,16], 1)]
theorem eval_atom0912 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20924470748160 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913 : SparsePolynomial.Poly := [([3,16,17], 1)]
theorem eval_atom0913 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58450854873600 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914 : SparsePolynomial.Poly := [([3,16,18], 1)]
theorem eval_atom0914 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 3) * (g 16) * (g 18)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58152523968000 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915 : SparsePolynomial.Poly := [([3,16,19], 1)]
theorem eval_atom0915 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 3) * (g 16) * (g 19)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40238672947200 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916 : SparsePolynomial.Poly := [([3,16,20], 1)]
theorem eval_atom0916 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 3) * (g 16) * (g 20)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46263971577600 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917 : SparsePolynomial.Poly := [([3,17,17], 1)]
theorem eval_atom0917 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39608547955200 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918 : SparsePolynomial.Poly := [([3,17,18], 1)]
theorem eval_atom0918 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 3) * (g 17) * (g 18)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61172435520000 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919 : SparsePolynomial.Poly := [([3,17,19], 1)]
theorem eval_atom0919 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 3) * (g 17) * (g 19)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40507146086400 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920 : SparsePolynomial.Poly := [([3,17,20], 1)]
theorem eval_atom0920 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 3) * (g 17) * (g 20)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51452745523200 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921 : SparsePolynomial.Poly := [([3,18,18], 1)]
theorem eval_atom0921 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 3) * (g 18) * (g 18)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18834575155200 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922 : SparsePolynomial.Poly := [([3,18,19], 1)]
theorem eval_atom0922 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 3) * (g 18) * (g 19)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22849293196800 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923 : SparsePolynomial.Poly := [([3,18,20], 1)]
theorem eval_atom0923 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 3) * (g 18) * (g 20)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35421140160000 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924 : SparsePolynomial.Poly := [([3,19,20], 1)]
theorem eval_atom0924 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 3) * (g 19) * (g 20)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12570880492800 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925 : SparsePolynomial.Poly := [([3,20,20], 1)]
theorem eval_atom0925 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 3) * (g 20) * (g 20)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13316995641600 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0926 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1394616787200 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom0927 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (954758619648 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0928 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (923143737600 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0929 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom0929 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1922698975104 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0930 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1970633145600 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931 : SparsePolynomial.Poly := [([4,4,9], 1)]
theorem eval_atom0931 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1943571974400 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932 : SparsePolynomial.Poly := [([4,4,10], 1)]
theorem eval_atom0932 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 4) * (g 4) * (g 10)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1916510803200 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933 : SparsePolynomial.Poly := [([4,4,11], 1)]
theorem eval_atom0933 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1577526048000 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934 : SparsePolynomial.Poly := [([4,4,15], 1)]
theorem eval_atom0934 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 4) * (g 4) * (g 15)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3145981960800 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0935 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2427545373696 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0936 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3197822282496 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937 : SparsePolynomial.Poly := [([4,5,9], 1)]
theorem eval_atom0937 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1516392057600 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom0938 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1573413811200 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom0939 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1736273548800 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940 : SparsePolynomial.Poly := [([4,5,13], 1)]
theorem eval_atom0940 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165266438400 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941 : SparsePolynomial.Poly := [([4,5,14], 1)]
theorem eval_atom0941 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592446355200 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942 : SparsePolynomial.Poly := [([4,5,15], 1)]
theorem eval_atom0942 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8758268900352 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943 : SparsePolynomial.Poly := [([4,5,16], 1)]
theorem eval_atom0943 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3991786230240 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944 : SparsePolynomial.Poly := [([4,5,17], 1)]
theorem eval_atom0944 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6523606342656 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945 : SparsePolynomial.Poly := [([4,5,18], 1)]
theorem eval_atom0945 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 4) * (g 5) * (g 18)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9974479623840 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946 : SparsePolynomial.Poly := [([4,5,19], 1)]
theorem eval_atom0946 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 4) * (g 5) * (g 19)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13828223276064 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947 : SparsePolynomial.Poly := [([4,5,20], 1)]
theorem eval_atom0947 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 4) * (g 5) * (g 20)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17685804276000 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0948 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5472155404800 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0949 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8096350811904 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0950 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4467831580800 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom0951 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2082106252800 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom0952 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2657156140800 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom0953 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2661268377600 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954 : SparsePolynomial.Poly := [([4,6,12], 1)]
theorem eval_atom0954 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1769936313600 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955 : SparsePolynomial.Poly := [([4,6,13], 1)]
theorem eval_atom0955 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2456130297600 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956 : SparsePolynomial.Poly := [([4,6,14], 1)]
theorem eval_atom0956 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3142324281600 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957 : SparsePolynomial.Poly := [([4,6,15], 1)]
theorem eval_atom0957 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12877580620800 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958 : SparsePolynomial.Poly := [([4,6,16], 1)]
theorem eval_atom0958 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8729970328800 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959 : SparsePolynomial.Poly := [([4,6,17], 1)]
theorem eval_atom0959 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12355275340800 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960 : SparsePolynomial.Poly := [([4,6,18], 1)]
theorem eval_atom0960 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 4) * (g 6) * (g 18)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18532874455200 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961 : SparsePolynomial.Poly := [([4,6,19], 1)]
theorem eval_atom0961 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 4) * (g 6) * (g 19)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24839412544800 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962 : SparsePolynomial.Poly := [([4,6,20], 1)]
theorem eval_atom0962 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 4) * (g 6) * (g 20)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31145950634400 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0963 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6636980507904 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0964 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10513332203904 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom0965 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8483261128704 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom0966 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8890145167104 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom0967 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9244119688704 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968 : SparsePolynomial.Poly := [([4,7,12], 1)]
theorem eval_atom0968 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8443635842304 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969 : SparsePolynomial.Poly := [([4,7,13], 1)]
theorem eval_atom0969 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9220678043904 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970 : SparsePolynomial.Poly := [([4,7,14], 1)]
theorem eval_atom0970 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9997720245504 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971 : SparsePolynomial.Poly := [([4,7,15], 1)]
theorem eval_atom0971 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19013184407808 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972 : SparsePolynomial.Poly := [([4,7,16], 1)]
theorem eval_atom0972 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15624546121440 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973 : SparsePolynomial.Poly := [([4,7,17], 1)]
theorem eval_atom0973 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20172537623808 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974 : SparsePolynomial.Poly := [([4,7,18], 1)]
theorem eval_atom0974 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 4) * (g 7) * (g 18)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25324113470112 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0975 : SparsePolynomial.Poly := [([4,7,19], 1)]
theorem eval_atom0975 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 4) * (g 7) * (g 19)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31531477635360 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block013 : SparsePolynomial.Poly := [([3,13,18], 47411171942400), ([3,13,19], 44102287944000), ([3,13,20], 53975438899200), ([3,14,14], 26303458406400), ([3,14,15], 48520679961600), ([3,14,16], 39984813388800), ([3,14,17], 58281619737600), ([3,14,18], 53383959014400), ([3,14,19], 44697323059200), ([3,14,20], 59921164800000), ([3,15,15], 30559794048000), ([3,15,16], 52085022796800), ([3,15,17], 72395953459200), ([3,15,18], 66129770649600), ([3,15,19], 43317203328000), ([3,15,20], 63125980646400), ([3,16,16], 20924470748160), ([3,16,17], 58450854873600), ([3,16,18], 58152523968000), ([3,16,19], 40238672947200), ([3,16,20], 46263971577600), ([3,17,17], 39608547955200), ([3,17,18], 61172435520000), ([3,17,19], 40507146086400), ([3,17,20], 51452745523200), ([3,18,18], 18834575155200), ([3,18,19], 22849293196800), ([3,18,20], 35421140160000), ([3,19,20], 12570880492800), ([3,20,20], 13316995641600), ([4,4,4], 1394616787200), ([4,4,5], 954758619648), ([4,4,6], 923143737600), ([4,4,7], 1922698975104), ([4,4,8], 1970633145600), ([4,4,9], 1943571974400), ([4,4,10], 1916510803200), ([4,4,11], 1577526048000), ([4,4,15], 3145981960800), ([4,5,5], 2427545373696), ([4,5,6], 3197822282496), ([4,5,9], 1516392057600), ([4,5,10], 1573413811200), ([4,5,11], 1736273548800), ([4,5,13], 165266438400), ([4,5,14], 592446355200), ([4,5,15], 8758268900352), ([4,5,16], 3991786230240), ([4,5,17], 6523606342656), ([4,5,18], 9974479623840), ([4,5,19], 13828223276064), ([4,5,20], 17685804276000), ([4,6,6], 5472155404800), ([4,6,7], 8096350811904), ([4,6,8], 4467831580800), ([4,6,9], 2082106252800), ([4,6,10], 2657156140800), ([4,6,11], 2661268377600), ([4,6,12], 1769936313600), ([4,6,13], 2456130297600), ([4,6,14], 3142324281600), ([4,6,15], 12877580620800), ([4,6,16], 8729970328800), ([4,6,17], 12355275340800), ([4,6,18], 18532874455200), ([4,6,19], 24839412544800), ([4,6,20], 31145950634400), ([4,7,7], 6636980507904), ([4,7,8], 10513332203904), ([4,7,9], 8483261128704), ([4,7,10], 8890145167104), ([4,7,11], 9244119688704), ([4,7,12], 8443635842304), ([4,7,13], 9220678043904), ([4,7,14], 9997720245504), ([4,7,15], 19013184407808), ([4,7,16], 15624546121440), ([4,7,17], 20172537623808), ([4,7,18], 25324113470112), ([4,7,19], 31531477635360)]
theorem block013_data : block013 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47411171942400 : Int) atom0896) (SparsePolynomial.scale (44102287944000 : Int) atom0897)) (SparsePolynomial.merge (SparsePolynomial.scale (53975438899200 : Int) atom0898) (SparsePolynomial.merge (SparsePolynomial.scale (26303458406400 : Int) atom0899) (SparsePolynomial.scale (48520679961600 : Int) atom0900)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39984813388800 : Int) atom0901) (SparsePolynomial.scale (58281619737600 : Int) atom0902)) (SparsePolynomial.merge (SparsePolynomial.scale (53383959014400 : Int) atom0903) (SparsePolynomial.merge (SparsePolynomial.scale (44697323059200 : Int) atom0904) (SparsePolynomial.scale (59921164800000 : Int) atom0905))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30559794048000 : Int) atom0906) (SparsePolynomial.scale (52085022796800 : Int) atom0907)) (SparsePolynomial.merge (SparsePolynomial.scale (72395953459200 : Int) atom0908) (SparsePolynomial.merge (SparsePolynomial.scale (66129770649600 : Int) atom0909) (SparsePolynomial.scale (43317203328000 : Int) atom0910)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (63125980646400 : Int) atom0911) (SparsePolynomial.scale (20924470748160 : Int) atom0912)) (SparsePolynomial.merge (SparsePolynomial.scale (58450854873600 : Int) atom0913) (SparsePolynomial.merge (SparsePolynomial.scale (58152523968000 : Int) atom0914) (SparsePolynomial.scale (40238672947200 : Int) atom0915)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46263971577600 : Int) atom0916) (SparsePolynomial.scale (39608547955200 : Int) atom0917)) (SparsePolynomial.merge (SparsePolynomial.scale (61172435520000 : Int) atom0918) (SparsePolynomial.merge (SparsePolynomial.scale (40507146086400 : Int) atom0919) (SparsePolynomial.scale (51452745523200 : Int) atom0920)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18834575155200 : Int) atom0921) (SparsePolynomial.scale (22849293196800 : Int) atom0922)) (SparsePolynomial.merge (SparsePolynomial.scale (35421140160000 : Int) atom0923) (SparsePolynomial.merge (SparsePolynomial.scale (12570880492800 : Int) atom0924) (SparsePolynomial.scale (13316995641600 : Int) atom0925))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1394616787200 : Int) atom0926) (SparsePolynomial.scale (954758619648 : Int) atom0927)) (SparsePolynomial.merge (SparsePolynomial.scale (923143737600 : Int) atom0928) (SparsePolynomial.merge (SparsePolynomial.scale (1922698975104 : Int) atom0929) (SparsePolynomial.scale (1970633145600 : Int) atom0930)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1943571974400 : Int) atom0931) (SparsePolynomial.scale (1916510803200 : Int) atom0932)) (SparsePolynomial.merge (SparsePolynomial.scale (1577526048000 : Int) atom0933) (SparsePolynomial.merge (SparsePolynomial.scale (3145981960800 : Int) atom0934) (SparsePolynomial.scale (2427545373696 : Int) atom0935))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3197822282496 : Int) atom0936) (SparsePolynomial.scale (1516392057600 : Int) atom0937)) (SparsePolynomial.merge (SparsePolynomial.scale (1573413811200 : Int) atom0938) (SparsePolynomial.merge (SparsePolynomial.scale (1736273548800 : Int) atom0939) (SparsePolynomial.scale (165266438400 : Int) atom0940)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (592446355200 : Int) atom0941) (SparsePolynomial.scale (8758268900352 : Int) atom0942)) (SparsePolynomial.merge (SparsePolynomial.scale (3991786230240 : Int) atom0943) (SparsePolynomial.merge (SparsePolynomial.scale (6523606342656 : Int) atom0944) (SparsePolynomial.scale (9974479623840 : Int) atom0945))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13828223276064 : Int) atom0946) (SparsePolynomial.scale (17685804276000 : Int) atom0947)) (SparsePolynomial.merge (SparsePolynomial.scale (5472155404800 : Int) atom0948) (SparsePolynomial.merge (SparsePolynomial.scale (8096350811904 : Int) atom0949) (SparsePolynomial.scale (4467831580800 : Int) atom0950)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2082106252800 : Int) atom0951) (SparsePolynomial.scale (2657156140800 : Int) atom0952)) (SparsePolynomial.merge (SparsePolynomial.scale (2661268377600 : Int) atom0953) (SparsePolynomial.merge (SparsePolynomial.scale (1769936313600 : Int) atom0954) (SparsePolynomial.scale (2456130297600 : Int) atom0955)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3142324281600 : Int) atom0956) (SparsePolynomial.scale (12877580620800 : Int) atom0957)) (SparsePolynomial.merge (SparsePolynomial.scale (8729970328800 : Int) atom0958) (SparsePolynomial.merge (SparsePolynomial.scale (12355275340800 : Int) atom0959) (SparsePolynomial.scale (18532874455200 : Int) atom0960)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24839412544800 : Int) atom0961) (SparsePolynomial.scale (31145950634400 : Int) atom0962)) (SparsePolynomial.merge (SparsePolynomial.scale (6636980507904 : Int) atom0963) (SparsePolynomial.merge (SparsePolynomial.scale (10513332203904 : Int) atom0964) (SparsePolynomial.scale (8483261128704 : Int) atom0965))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8890145167104 : Int) atom0966) (SparsePolynomial.scale (9244119688704 : Int) atom0967)) (SparsePolynomial.merge (SparsePolynomial.scale (8443635842304 : Int) atom0968) (SparsePolynomial.merge (SparsePolynomial.scale (9220678043904 : Int) atom0969) (SparsePolynomial.scale (9997720245504 : Int) atom0970)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19013184407808 : Int) atom0971) (SparsePolynomial.scale (15624546121440 : Int) atom0972)) (SparsePolynomial.merge (SparsePolynomial.scale (20172537623808 : Int) atom0973) (SparsePolynomial.merge (SparsePolynomial.scale (25324113470112 : Int) atom0974) (SparsePolynomial.scale (31531477635360 : Int) atom0975)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block013 := by
  rw [block013_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0896_nonneg g hg hA hB) (atom0897_nonneg g hg hA hB)) (add_nonneg (atom0898_nonneg g hg hA hB) (add_nonneg (atom0899_nonneg g hg hA hB) (atom0900_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0901_nonneg g hg hA hB) (atom0902_nonneg g hg hA hB)) (add_nonneg (atom0903_nonneg g hg hA hB) (add_nonneg (atom0904_nonneg g hg hA hB) (atom0905_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0906_nonneg g hg hA hB) (atom0907_nonneg g hg hA hB)) (add_nonneg (atom0908_nonneg g hg hA hB) (add_nonneg (atom0909_nonneg g hg hA hB) (atom0910_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0911_nonneg g hg hA hB) (atom0912_nonneg g hg hA hB)) (add_nonneg (atom0913_nonneg g hg hA hB) (add_nonneg (atom0914_nonneg g hg hA hB) (atom0915_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0916_nonneg g hg hA hB) (atom0917_nonneg g hg hA hB)) (add_nonneg (atom0918_nonneg g hg hA hB) (add_nonneg (atom0919_nonneg g hg hA hB) (atom0920_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0921_nonneg g hg hA hB) (atom0922_nonneg g hg hA hB)) (add_nonneg (atom0923_nonneg g hg hA hB) (add_nonneg (atom0924_nonneg g hg hA hB) (atom0925_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0926_nonneg g hg hA hB) (atom0927_nonneg g hg hA hB)) (add_nonneg (atom0928_nonneg g hg hA hB) (add_nonneg (atom0929_nonneg g hg hA hB) (atom0930_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0931_nonneg g hg hA hB) (atom0932_nonneg g hg hA hB)) (add_nonneg (atom0933_nonneg g hg hA hB) (add_nonneg (atom0934_nonneg g hg hA hB) (atom0935_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0936_nonneg g hg hA hB) (atom0937_nonneg g hg hA hB)) (add_nonneg (atom0938_nonneg g hg hA hB) (add_nonneg (atom0939_nonneg g hg hA hB) (atom0940_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0941_nonneg g hg hA hB) (atom0942_nonneg g hg hA hB)) (add_nonneg (atom0943_nonneg g hg hA hB) (add_nonneg (atom0944_nonneg g hg hA hB) (atom0945_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0946_nonneg g hg hA hB) (atom0947_nonneg g hg hA hB)) (add_nonneg (atom0948_nonneg g hg hA hB) (add_nonneg (atom0949_nonneg g hg hA hB) (atom0950_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0951_nonneg g hg hA hB) (atom0952_nonneg g hg hA hB)) (add_nonneg (atom0953_nonneg g hg hA hB) (add_nonneg (atom0954_nonneg g hg hA hB) (atom0955_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0956_nonneg g hg hA hB) (atom0957_nonneg g hg hA hB)) (add_nonneg (atom0958_nonneg g hg hA hB) (add_nonneg (atom0959_nonneg g hg hA hB) (atom0960_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0961_nonneg g hg hA hB) (atom0962_nonneg g hg hA hB)) (add_nonneg (atom0963_nonneg g hg hA hB) (add_nonneg (atom0964_nonneg g hg hA hB) (atom0965_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0966_nonneg g hg hA hB) (atom0967_nonneg g hg hA hB)) (add_nonneg (atom0968_nonneg g hg hA hB) (add_nonneg (atom0969_nonneg g hg hA hB) (atom0970_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0971_nonneg g hg hA hB) (atom0972_nonneg g hg hA hB)) (add_nonneg (atom0973_nonneg g hg hA hB) (add_nonneg (atom0974_nonneg g hg hA hB) (atom0975_nonneg g hg hA hB))))))))

end APPT.Finite21
