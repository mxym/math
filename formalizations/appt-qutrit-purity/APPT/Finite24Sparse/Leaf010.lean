import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0609 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0609 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0609 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0609_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (142598777207040 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0610 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0610 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0610_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121344224601600 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611 : SparsePolynomial.Poly := [([1,6,9], 1)]
theorem eval_atom0611 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0611 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0611_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129213729335592 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612 : SparsePolynomial.Poly := [([1,6,10], 1)]
theorem eval_atom0612 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0612 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0612_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156989643019704 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613 : SparsePolynomial.Poly := [([1,6,11], 1)]
theorem eval_atom0613 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0613 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0613_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (178123796942256 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614 : SparsePolynomial.Poly := [([1,6,12], 1)]
theorem eval_atom0614 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0614 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0614_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (218964915186336 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615 : SparsePolynomial.Poly := [([1,6,13], 1)]
theorem eval_atom0615 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0615 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0615_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205962588216000 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616 : SparsePolynomial.Poly := [([1,6,14], 1)]
theorem eval_atom0616 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0616 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0616_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (187448867020800 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617 : SparsePolynomial.Poly := [([1,6,15], 1)]
theorem eval_atom0617 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0617 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0617_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (191115655718400 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618 : SparsePolynomial.Poly := [([1,6,16], 1)]
theorem eval_atom0618 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0618 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0618_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177048679046400 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619 : SparsePolynomial.Poly := [([1,6,17], 1)]
theorem eval_atom0619 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0619 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0619_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (177880810060800 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620 : SparsePolynomial.Poly := [([1,6,18], 1)]
theorem eval_atom0620 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0620 = ((g 1) * (g 6) * (g 18)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0620_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (227305139846400 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621 : SparsePolynomial.Poly := [([1,6,19], 1)]
theorem eval_atom0621 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0621 = ((g 1) * (g 6) * (g 19)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0621_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (197144498073600 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622 : SparsePolynomial.Poly := [([1,6,20], 1)]
theorem eval_atom0622 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0622 = ((g 1) * (g 6) * (g 20)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0622_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (243868509561600 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623 : SparsePolynomial.Poly := [([1,6,21], 1)]
theorem eval_atom0623 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0623 = ((g 1) * (g 6) * (g 21)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0623_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (229597929792000 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624 : SparsePolynomial.Poly := [([1,6,22], 1)]
theorem eval_atom0624 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0624 = ((g 1) * (g 6) * (g 22)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0624_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (292791670752000 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625 : SparsePolynomial.Poly := [([1,6,23], 1)]
theorem eval_atom0625 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0625 = ((g 1) * (g 6) * (g 23)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0625_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (280178158176000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0626 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0626 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0626_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (97409907302400 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0627 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0627 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0627_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166327558467840 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628 : SparsePolynomial.Poly := [([1,7,9], 1)]
theorem eval_atom0628 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0628 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0628_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145263690951720 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629 : SparsePolynomial.Poly := [([1,7,10], 1)]
theorem eval_atom0629 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0629 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0629_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170879862994104 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630 : SparsePolynomial.Poly := [([1,7,11], 1)]
theorem eval_atom0630 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0630 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0630_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193055872007856 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631 : SparsePolynomial.Poly := [([1,7,12], 1)]
theorem eval_atom0631 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0631 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0631_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (234938845343136 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632 : SparsePolynomial.Poly := [([1,7,13], 1)]
theorem eval_atom0632 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0632 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0632_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221947149547200 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633 : SparsePolynomial.Poly := [([1,7,14], 1)]
theorem eval_atom0633 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0633 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0633_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203444059526400 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634 : SparsePolynomial.Poly := [([1,7,15], 1)]
theorem eval_atom0634 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0634 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0634_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207121479398400 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635 : SparsePolynomial.Poly := [([1,7,16], 1)]
theorem eval_atom0635 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0635 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0635_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193065133900800 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636 : SparsePolynomial.Poly := [([1,7,17], 1)]
theorem eval_atom0636 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0636 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0636_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193907896089600 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637 : SparsePolynomial.Poly := [([1,7,18], 1)]
theorem eval_atom0637 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0637 = ((g 1) * (g 7) * (g 18)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0637_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (244507561267200 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638 : SparsePolynomial.Poly := [([1,7,19], 1)]
theorem eval_atom0638 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0638 = ((g 1) * (g 7) * (g 19)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0638_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (216686959104000 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639 : SparsePolynomial.Poly := [([1,7,20], 1)]
theorem eval_atom0639 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0639 = ((g 1) * (g 7) * (g 20)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0639_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (265751010201600 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640 : SparsePolynomial.Poly := [([1,7,21], 1)]
theorem eval_atom0640 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0640 = ((g 1) * (g 7) * (g 21)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0640_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256149878476800 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641 : SparsePolynomial.Poly := [([1,7,22], 1)]
theorem eval_atom0641 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0641 = ((g 1) * (g 7) * (g 22)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0641_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (326703148352000 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642 : SparsePolynomial.Poly := [([1,7,23], 1)]
theorem eval_atom0642 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0642 = ((g 1) * (g 7) * (g 23)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0642_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (316265679676800 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0643 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0643 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0643_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (113923664870400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644 : SparsePolynomial.Poly := [([1,8,9], 1)]
theorem eval_atom0644 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0644 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0644_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (204854516840160 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645 : SparsePolynomial.Poly := [([1,8,10], 1)]
theorem eval_atom0645 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0645 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0645_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188840203618968 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646 : SparsePolynomial.Poly := [([1,8,11], 1)]
theorem eval_atom0646 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0646 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0646_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207125640705456 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647 : SparsePolynomial.Poly := [([1,8,12], 1)]
theorem eval_atom0647 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0647 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0647_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (246967428555936 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648 : SparsePolynomial.Poly := [([1,8,13], 1)]
theorem eval_atom0648 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0648 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0648_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (233476067563200 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649 : SparsePolynomial.Poly := [([1,8,14], 1)]
theorem eval_atom0649 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0649 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0649_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (214473312345600 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650 : SparsePolynomial.Poly := [([1,8,15], 1)]
theorem eval_atom0650 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0650 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0650_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (217651067020800 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651 : SparsePolynomial.Poly := [([1,8,16], 1)]
theorem eval_atom0651 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0651 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0651_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203095056326400 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652 : SparsePolynomial.Poly := [([1,8,17], 1)]
theorem eval_atom0652 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0652 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0652_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203438153318400 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653 : SparsePolynomial.Poly := [([1,8,18], 1)]
theorem eval_atom0653 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0653 = ((g 1) * (g 8) * (g 18)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0653_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (255265128518400 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654 : SparsePolynomial.Poly := [([1,8,19], 1)]
theorem eval_atom0654 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0654 = ((g 1) * (g 8) * (g 19)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0654_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230398811596800 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655 : SparsePolynomial.Poly := [([1,8,20], 1)]
theorem eval_atom0655 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0655 = ((g 1) * (g 8) * (g 20)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0655_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (282417147936000 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656 : SparsePolynomial.Poly := [([1,8,21], 1)]
theorem eval_atom0656 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0656 = ((g 1) * (g 8) * (g 21)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0656_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (279224251891200 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657 : SparsePolynomial.Poly := [([1,8,22], 1)]
theorem eval_atom0657 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0657 = ((g 1) * (g 8) * (g 22)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0657_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (356557454803200 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658 : SparsePolynomial.Poly := [([1,8,23], 1)]
theorem eval_atom0658 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0658 = ((g 1) * (g 8) * (g 23)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0658_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (349745019724800 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659 : SparsePolynomial.Poly := [([1,9,9], 1)]
theorem eval_atom0659 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0659 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0659_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136999274369760 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660 : SparsePolynomial.Poly := [([1,9,10], 1)]
theorem eval_atom0660 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0660 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0660_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (255486130384320 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661 : SparsePolynomial.Poly := [([1,9,11], 1)]
theorem eval_atom0661 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0661 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0661_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (242659403316000 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662 : SparsePolynomial.Poly := [([1,9,12], 1)]
theorem eval_atom0662 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0662 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0662_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (272104064602128 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663 : SparsePolynomial.Poly := [([1,9,13], 1)]
theorem eval_atom0663 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0663 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0663_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256061221753392 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664 : SparsePolynomial.Poly := [([1,9,14], 1)]
theorem eval_atom0664 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0664 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0664_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (236048504967792 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665 : SparsePolynomial.Poly := [([1,9,15], 1)]
theorem eval_atom0665 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0665 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0665_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238216298074992 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666 : SparsePolynomial.Poly := [([1,9,16], 1)]
theorem eval_atom0666 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0666 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0666_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (222650325812592 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667 : SparsePolynomial.Poly := [([1,9,17], 1)]
theorem eval_atom0667 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0667 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0667_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221983461236592 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668 : SparsePolynomial.Poly := [([1,9,18], 1)]
theorem eval_atom0668 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0668 = ((g 1) * (g 9) * (g 18)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0668_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (273902208783984 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669 : SparsePolynomial.Poly := [([1,9,19], 1)]
theorem eval_atom0669 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0669 = ((g 1) * (g 9) * (g 19)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0669_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (250229398125168 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670 : SparsePolynomial.Poly := [([1,9,20], 1)]
theorem eval_atom0670 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0670 = ((g 1) * (g 9) * (g 20)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0670_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (303441240727152 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671 : SparsePolynomial.Poly := [([1,9,21], 1)]
theorem eval_atom0671 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0671 = ((g 1) * (g 9) * (g 21)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0671_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (303645318775920 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672 : SparsePolynomial.Poly := [([1,9,22], 1)]
theorem eval_atom0672 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0672 = ((g 1) * (g 9) * (g 22)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0672_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (368500279875840 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673 : SparsePolynomial.Poly := [([1,9,23], 1)]
theorem eval_atom0673 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0673 = ((g 1) * (g 9) * (g 23)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0673_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (362803493738880 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674 : SparsePolynomial.Poly := [([1,10,10], 1)]
theorem eval_atom0674 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0674 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0674_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164555278414560 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675 : SparsePolynomial.Poly := [([1,10,11], 1)]
theorem eval_atom0675 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0675 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0675_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (316431248712480 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676 : SparsePolynomial.Poly := [([1,10,12], 1)]
theorem eval_atom0676 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0676 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0676_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (322461649501200 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677 : SparsePolynomial.Poly := [([1,10,13], 1)]
theorem eval_atom0677 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0677 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0677_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (304203431906352 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678 : SparsePolynomial.Poly := [([1,10,14], 1)]
theorem eval_atom0678 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0678 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0678_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (282670457181552 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679 : SparsePolynomial.Poly := [([1,10,15], 1)]
theorem eval_atom0679 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0679 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0679_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (283317992349552 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680 : SparsePolynomial.Poly := [([1,10,16], 1)]
theorem eval_atom0680 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0680 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0680_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (266231762147952 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681 : SparsePolynomial.Poly := [([1,10,17], 1)]
theorem eval_atom0681 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0681 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0681_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264044639632752 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682 : SparsePolynomial.Poly := [([1,10,18], 1)]
theorem eval_atom0682 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0682 = ((g 1) * (g 10) * (g 18)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0682_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (313809511246704 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683 : SparsePolynomial.Poly := [([1,10,19], 1)]
theorem eval_atom0683 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0683 = ((g 1) * (g 10) * (g 19)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0683_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (287349206660208 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684 : SparsePolynomial.Poly := [([1,10,20], 1)]
theorem eval_atom0684 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0684 = ((g 1) * (g 10) * (g 20)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0684_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (337773555334512 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685 : SparsePolynomial.Poly := [([1,10,21], 1)]
theorem eval_atom0685 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0685 = ((g 1) * (g 10) * (g 21)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0685_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (333922903467120 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686 : SparsePolynomial.Poly := [([1,10,22], 1)]
theorem eval_atom0686 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0686 = ((g 1) * (g 10) * (g 22)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0686_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (349580333168640 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687 : SparsePolynomial.Poly := [([1,10,23], 1)]
theorem eval_atom0687 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0687 = ((g 1) * (g 10) * (g 23)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0687_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (338789442631680 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688 : SparsePolynomial.Poly := [([1,11,11], 1)]
theorem eval_atom0688 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0688 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0688_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (201506544866880 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block010 : SparsePolynomial.Poly := [([1,6,7], 142598777207040), ([1,6,8], 121344224601600), ([1,6,9], 129213729335592), ([1,6,10], 156989643019704), ([1,6,11], 178123796942256), ([1,6,12], 218964915186336), ([1,6,13], 205962588216000), ([1,6,14], 187448867020800), ([1,6,15], 191115655718400), ([1,6,16], 177048679046400), ([1,6,17], 177880810060800), ([1,6,18], 227305139846400), ([1,6,19], 197144498073600), ([1,6,20], 243868509561600), ([1,6,21], 229597929792000), ([1,6,22], 292791670752000), ([1,6,23], 280178158176000), ([1,7,7], 97409907302400), ([1,7,8], 166327558467840), ([1,7,9], 145263690951720), ([1,7,10], 170879862994104), ([1,7,11], 193055872007856), ([1,7,12], 234938845343136), ([1,7,13], 221947149547200), ([1,7,14], 203444059526400), ([1,7,15], 207121479398400), ([1,7,16], 193065133900800), ([1,7,17], 193907896089600), ([1,7,18], 244507561267200), ([1,7,19], 216686959104000), ([1,7,20], 265751010201600), ([1,7,21], 256149878476800), ([1,7,22], 326703148352000), ([1,7,23], 316265679676800), ([1,8,8], 113923664870400), ([1,8,9], 204854516840160), ([1,8,10], 188840203618968), ([1,8,11], 207125640705456), ([1,8,12], 246967428555936), ([1,8,13], 233476067563200), ([1,8,14], 214473312345600), ([1,8,15], 217651067020800), ([1,8,16], 203095056326400), ([1,8,17], 203438153318400), ([1,8,18], 255265128518400), ([1,8,19], 230398811596800), ([1,8,20], 282417147936000), ([1,8,21], 279224251891200), ([1,8,22], 356557454803200), ([1,8,23], 349745019724800), ([1,9,9], 136999274369760), ([1,9,10], 255486130384320), ([1,9,11], 242659403316000), ([1,9,12], 272104064602128), ([1,9,13], 256061221753392), ([1,9,14], 236048504967792), ([1,9,15], 238216298074992), ([1,9,16], 222650325812592), ([1,9,17], 221983461236592), ([1,9,18], 273902208783984), ([1,9,19], 250229398125168), ([1,9,20], 303441240727152), ([1,9,21], 303645318775920), ([1,9,22], 368500279875840), ([1,9,23], 362803493738880), ([1,10,10], 164555278414560), ([1,10,11], 316431248712480), ([1,10,12], 322461649501200), ([1,10,13], 304203431906352), ([1,10,14], 282670457181552), ([1,10,15], 283317992349552), ([1,10,16], 266231762147952), ([1,10,17], 264044639632752), ([1,10,18], 313809511246704), ([1,10,19], 287349206660208), ([1,10,20], 337773555334512), ([1,10,21], 333922903467120), ([1,10,22], 349580333168640), ([1,10,23], 338789442631680), ([1,11,11], 201506544866880)]
theorem block010_data : block010 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142598777207040 : Int) atom0609) (SparsePolynomial.scale (121344224601600 : Int) atom0610)) (SparsePolynomial.merge (SparsePolynomial.scale (129213729335592 : Int) atom0611) (SparsePolynomial.merge (SparsePolynomial.scale (156989643019704 : Int) atom0612) (SparsePolynomial.scale (178123796942256 : Int) atom0613)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (218964915186336 : Int) atom0614) (SparsePolynomial.scale (205962588216000 : Int) atom0615)) (SparsePolynomial.merge (SparsePolynomial.scale (187448867020800 : Int) atom0616) (SparsePolynomial.merge (SparsePolynomial.scale (191115655718400 : Int) atom0617) (SparsePolynomial.scale (177048679046400 : Int) atom0618))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (177880810060800 : Int) atom0619) (SparsePolynomial.scale (227305139846400 : Int) atom0620)) (SparsePolynomial.merge (SparsePolynomial.scale (197144498073600 : Int) atom0621) (SparsePolynomial.merge (SparsePolynomial.scale (243868509561600 : Int) atom0622) (SparsePolynomial.scale (229597929792000 : Int) atom0623)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (292791670752000 : Int) atom0624) (SparsePolynomial.scale (280178158176000 : Int) atom0625)) (SparsePolynomial.merge (SparsePolynomial.scale (97409907302400 : Int) atom0626) (SparsePolynomial.merge (SparsePolynomial.scale (166327558467840 : Int) atom0627) (SparsePolynomial.scale (145263690951720 : Int) atom0628)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (170879862994104 : Int) atom0629) (SparsePolynomial.scale (193055872007856 : Int) atom0630)) (SparsePolynomial.merge (SparsePolynomial.scale (234938845343136 : Int) atom0631) (SparsePolynomial.merge (SparsePolynomial.scale (221947149547200 : Int) atom0632) (SparsePolynomial.scale (203444059526400 : Int) atom0633)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (207121479398400 : Int) atom0634) (SparsePolynomial.scale (193065133900800 : Int) atom0635)) (SparsePolynomial.merge (SparsePolynomial.scale (193907896089600 : Int) atom0636) (SparsePolynomial.merge (SparsePolynomial.scale (244507561267200 : Int) atom0637) (SparsePolynomial.scale (216686959104000 : Int) atom0638))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (265751010201600 : Int) atom0639) (SparsePolynomial.scale (256149878476800 : Int) atom0640)) (SparsePolynomial.merge (SparsePolynomial.scale (326703148352000 : Int) atom0641) (SparsePolynomial.merge (SparsePolynomial.scale (316265679676800 : Int) atom0642) (SparsePolynomial.scale (113923664870400 : Int) atom0643)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (204854516840160 : Int) atom0644) (SparsePolynomial.scale (188840203618968 : Int) atom0645)) (SparsePolynomial.merge (SparsePolynomial.scale (207125640705456 : Int) atom0646) (SparsePolynomial.merge (SparsePolynomial.scale (246967428555936 : Int) atom0647) (SparsePolynomial.scale (233476067563200 : Int) atom0648))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (214473312345600 : Int) atom0649) (SparsePolynomial.scale (217651067020800 : Int) atom0650)) (SparsePolynomial.merge (SparsePolynomial.scale (203095056326400 : Int) atom0651) (SparsePolynomial.merge (SparsePolynomial.scale (203438153318400 : Int) atom0652) (SparsePolynomial.scale (255265128518400 : Int) atom0653)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (230398811596800 : Int) atom0654) (SparsePolynomial.scale (282417147936000 : Int) atom0655)) (SparsePolynomial.merge (SparsePolynomial.scale (279224251891200 : Int) atom0656) (SparsePolynomial.merge (SparsePolynomial.scale (356557454803200 : Int) atom0657) (SparsePolynomial.scale (349745019724800 : Int) atom0658))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (136999274369760 : Int) atom0659) (SparsePolynomial.scale (255486130384320 : Int) atom0660)) (SparsePolynomial.merge (SparsePolynomial.scale (242659403316000 : Int) atom0661) (SparsePolynomial.merge (SparsePolynomial.scale (272104064602128 : Int) atom0662) (SparsePolynomial.scale (256061221753392 : Int) atom0663)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (236048504967792 : Int) atom0664) (SparsePolynomial.scale (238216298074992 : Int) atom0665)) (SparsePolynomial.merge (SparsePolynomial.scale (222650325812592 : Int) atom0666) (SparsePolynomial.merge (SparsePolynomial.scale (221983461236592 : Int) atom0667) (SparsePolynomial.scale (273902208783984 : Int) atom0668)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (250229398125168 : Int) atom0669) (SparsePolynomial.scale (303441240727152 : Int) atom0670)) (SparsePolynomial.merge (SparsePolynomial.scale (303645318775920 : Int) atom0671) (SparsePolynomial.merge (SparsePolynomial.scale (368500279875840 : Int) atom0672) (SparsePolynomial.scale (362803493738880 : Int) atom0673)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (164555278414560 : Int) atom0674) (SparsePolynomial.scale (316431248712480 : Int) atom0675)) (SparsePolynomial.merge (SparsePolynomial.scale (322461649501200 : Int) atom0676) (SparsePolynomial.merge (SparsePolynomial.scale (304203431906352 : Int) atom0677) (SparsePolynomial.scale (282670457181552 : Int) atom0678))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (283317992349552 : Int) atom0679) (SparsePolynomial.scale (266231762147952 : Int) atom0680)) (SparsePolynomial.merge (SparsePolynomial.scale (264044639632752 : Int) atom0681) (SparsePolynomial.merge (SparsePolynomial.scale (313809511246704 : Int) atom0682) (SparsePolynomial.scale (287349206660208 : Int) atom0683)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (337773555334512 : Int) atom0684) (SparsePolynomial.scale (333922903467120 : Int) atom0685)) (SparsePolynomial.merge (SparsePolynomial.scale (349580333168640 : Int) atom0686) (SparsePolynomial.merge (SparsePolynomial.scale (338789442631680 : Int) atom0687) (SparsePolynomial.scale (201506544866880 : Int) atom0688)))))))) := by decide +kernel
theorem block010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block010 := by
  rw [block010_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0609_nonneg g hg hA hB) (atom0610_nonneg g hg hA hB)) (add_nonneg (atom0611_nonneg g hg hA hB) (add_nonneg (atom0612_nonneg g hg hA hB) (atom0613_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0614_nonneg g hg hA hB) (atom0615_nonneg g hg hA hB)) (add_nonneg (atom0616_nonneg g hg hA hB) (add_nonneg (atom0617_nonneg g hg hA hB) (atom0618_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0619_nonneg g hg hA hB) (atom0620_nonneg g hg hA hB)) (add_nonneg (atom0621_nonneg g hg hA hB) (add_nonneg (atom0622_nonneg g hg hA hB) (atom0623_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0624_nonneg g hg hA hB) (atom0625_nonneg g hg hA hB)) (add_nonneg (atom0626_nonneg g hg hA hB) (add_nonneg (atom0627_nonneg g hg hA hB) (atom0628_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0629_nonneg g hg hA hB) (atom0630_nonneg g hg hA hB)) (add_nonneg (atom0631_nonneg g hg hA hB) (add_nonneg (atom0632_nonneg g hg hA hB) (atom0633_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0634_nonneg g hg hA hB) (atom0635_nonneg g hg hA hB)) (add_nonneg (atom0636_nonneg g hg hA hB) (add_nonneg (atom0637_nonneg g hg hA hB) (atom0638_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0639_nonneg g hg hA hB) (atom0640_nonneg g hg hA hB)) (add_nonneg (atom0641_nonneg g hg hA hB) (add_nonneg (atom0642_nonneg g hg hA hB) (atom0643_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0644_nonneg g hg hA hB) (atom0645_nonneg g hg hA hB)) (add_nonneg (atom0646_nonneg g hg hA hB) (add_nonneg (atom0647_nonneg g hg hA hB) (atom0648_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0649_nonneg g hg hA hB) (atom0650_nonneg g hg hA hB)) (add_nonneg (atom0651_nonneg g hg hA hB) (add_nonneg (atom0652_nonneg g hg hA hB) (atom0653_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0654_nonneg g hg hA hB) (atom0655_nonneg g hg hA hB)) (add_nonneg (atom0656_nonneg g hg hA hB) (add_nonneg (atom0657_nonneg g hg hA hB) (atom0658_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0659_nonneg g hg hA hB) (atom0660_nonneg g hg hA hB)) (add_nonneg (atom0661_nonneg g hg hA hB) (add_nonneg (atom0662_nonneg g hg hA hB) (atom0663_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0664_nonneg g hg hA hB) (atom0665_nonneg g hg hA hB)) (add_nonneg (atom0666_nonneg g hg hA hB) (add_nonneg (atom0667_nonneg g hg hA hB) (atom0668_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0669_nonneg g hg hA hB) (atom0670_nonneg g hg hA hB)) (add_nonneg (atom0671_nonneg g hg hA hB) (add_nonneg (atom0672_nonneg g hg hA hB) (atom0673_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0674_nonneg g hg hA hB) (atom0675_nonneg g hg hA hB)) (add_nonneg (atom0676_nonneg g hg hA hB) (add_nonneg (atom0677_nonneg g hg hA hB) (atom0678_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0679_nonneg g hg hA hB) (atom0680_nonneg g hg hA hB)) (add_nonneg (atom0681_nonneg g hg hA hB) (add_nonneg (atom0682_nonneg g hg hA hB) (atom0683_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0684_nonneg g hg hA hB) (atom0685_nonneg g hg hA hB)) (add_nonneg (atom0686_nonneg g hg hA hB) (add_nonneg (atom0687_nonneg g hg hA hB) (atom0688_nonneg g hg hA hB))))))))

end APPT.Finite24
