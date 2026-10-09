import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0689 : SparsePolynomial.Poly := [([1,11,12], 1)]
theorem eval_atom0689 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0689 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0689_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (394708547851200 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690 : SparsePolynomial.Poly := [([1,11,13], 1)]
theorem eval_atom0690 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0690 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0690_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353450265078240 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691 : SparsePolynomial.Poly := [([1,11,14], 1)]
theorem eval_atom0691 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0691 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0691_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321640443169056 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692 : SparsePolynomial.Poly := [([1,11,15], 1)]
theorem eval_atom0692 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0692 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0692_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318715903738656 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693 : SparsePolynomial.Poly := [([1,11,16], 1)]
theorem eval_atom0693 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0693 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0693_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299599119226656 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694 : SparsePolynomial.Poly := [([1,11,17], 1)]
theorem eval_atom0694 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0694 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0694_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (295381442401056 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695 : SparsePolynomial.Poly := [([1,11,18], 1)]
theorem eval_atom0695 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0695 = ((g 1) * (g 11) * (g 18)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0695_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349182426719808 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696 : SparsePolynomial.Poly := [([1,11,19], 1)]
theorem eval_atom0696 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0696 = ((g 1) * (g 11) * (g 19)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0696_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315381779675424 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697 : SparsePolynomial.Poly := [([1,11,20], 1)]
theorem eval_atom0697 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0697 = ((g 1) * (g 11) * (g 20)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0697_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369424182777408 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698 : SparsePolynomial.Poly := [([1,11,21], 1)]
theorem eval_atom0698 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0698 = ((g 1) * (g 11) * (g 21)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0698_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (359408125596960 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699 : SparsePolynomial.Poly := [([1,11,22], 1)]
theorem eval_atom0699 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0699 = ((g 1) * (g 11) * (g 22)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0699_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330379014712320 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700 : SparsePolynomial.Poly := [([1,11,23], 1)]
theorem eval_atom0700 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0700 = ((g 1) * (g 11) * (g 23)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0700_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338126709026304 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701 : SparsePolynomial.Poly := [([1,12,12], 1)]
theorem eval_atom0701 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0701 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0701_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242832577553280 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702 : SparsePolynomial.Poly := [([1,12,13], 1)]
theorem eval_atom0702 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0702 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0702_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (435085192840320 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703 : SparsePolynomial.Poly := [([1,12,14], 1)]
theorem eval_atom0703 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0703 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0703_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (385560346343040 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704 : SparsePolynomial.Poly := [([1,12,15], 1)]
theorem eval_atom0704 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0704 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0704_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379386155583936 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705 : SparsePolynomial.Poly := [([1,12,16], 1)]
theorem eval_atom0705 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0705 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0705_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (357728520390336 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706 : SparsePolynomial.Poly := [([1,12,17], 1)]
theorem eval_atom0706 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0706 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0706_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350969992883136 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707 : SparsePolynomial.Poly := [([1,12,18], 1)]
theorem eval_atom0707 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0707 = ((g 1) * (g 12) * (g 18)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0707_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415062219800448 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708 : SparsePolynomial.Poly := [([1,12,19], 1)]
theorem eval_atom0708 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0708 = ((g 1) * (g 12) * (g 19)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0708_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361270446634944 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709 : SparsePolynomial.Poly := [([1,12,20], 1)]
theorem eval_atom0709 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0709 = ((g 1) * (g 12) * (g 20)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0709_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439386346827648 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710 : SparsePolynomial.Poly := [([1,12,21], 1)]
theorem eval_atom0710 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0710 = ((g 1) * (g 12) * (g 21)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0710_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390978726874560 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711 : SparsePolynomial.Poly := [([1,12,22], 1)]
theorem eval_atom0711 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0711 = ((g 1) * (g 12) * (g 22)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0711_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (325176814433280 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712 : SparsePolynomial.Poly := [([1,12,23], 1)]
theorem eval_atom0712 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0712 = ((g 1) * (g 12) * (g 23)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0712_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324378474292224 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713 : SparsePolynomial.Poly := [([1,13,13], 1)]
theorem eval_atom0713 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0713 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0713_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241883189856000 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714 : SparsePolynomial.Poly := [([1,13,14], 1)]
theorem eval_atom0714 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0714 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0714_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422611559979840 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715 : SparsePolynomial.Poly := [([1,13,15], 1)]
theorem eval_atom0715 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0715 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0715_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (385974487301760 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716 : SparsePolynomial.Poly := [([1,13,16], 1)]
theorem eval_atom0716 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0716 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0716_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358553364624000 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717 : SparsePolynomial.Poly := [([1,13,17], 1)]
theorem eval_atom0717 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0717 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0717_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (348743690064000 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718 : SparsePolynomial.Poly := [([1,13,18], 1)]
theorem eval_atom0718 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0718 = ((g 1) * (g 13) * (g 18)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0718_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407775787372800 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719 : SparsePolynomial.Poly := [([1,13,19], 1)]
theorem eval_atom0719 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0719 = ((g 1) * (g 13) * (g 19)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0719_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (355536072460800 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720 : SparsePolynomial.Poly := [([1,13,20], 1)]
theorem eval_atom0720 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0720 = ((g 1) * (g 13) * (g 20)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0720_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436182285369600 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721 : SparsePolynomial.Poly := [([1,13,21], 1)]
theorem eval_atom0721 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0721 = ((g 1) * (g 13) * (g 21)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0721_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (384330504096000 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722 : SparsePolynomial.Poly := [([1,13,22], 1)]
theorem eval_atom0722 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0722 = ((g 1) * (g 13) * (g 22)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0722_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327597538800000 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723 : SparsePolynomial.Poly := [([1,13,23], 1)]
theorem eval_atom0723 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0723 = ((g 1) * (g 13) * (g 23)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0723_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327207015273600 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724 : SparsePolynomial.Poly := [([1,14,14], 1)]
theorem eval_atom0724 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0724 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0724_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230358944692800 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725 : SparsePolynomial.Poly := [([1,14,15], 1)]
theorem eval_atom0725 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0725 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0725_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415536541842240 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726 : SparsePolynomial.Poly := [([1,14,16], 1)]
theorem eval_atom0726 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0726 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0726_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358531991415360 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727 : SparsePolynomial.Poly := [([1,14,17], 1)]
theorem eval_atom0727 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0727 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0727_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344356141852800 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728 : SparsePolynomial.Poly := [([1,14,18], 1)]
theorem eval_atom0728 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0728 = ((g 1) * (g 14) * (g 18)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0728_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393140829312000 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729 : SparsePolynomial.Poly := [([1,14,19], 1)]
theorem eval_atom0729 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0729 = ((g 1) * (g 14) * (g 19)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0729_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345302980822800 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730 : SparsePolynomial.Poly := [([1,14,20], 1)]
theorem eval_atom0730 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0730 = ((g 1) * (g 14) * (g 20)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0730_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425629698278400 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731 : SparsePolynomial.Poly := [([1,14,21], 1)]
theorem eval_atom0731 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0731 = ((g 1) * (g 14) * (g 21)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0731_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375819102489600 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732 : SparsePolynomial.Poly := [([1,14,22], 1)]
theorem eval_atom0732 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0732 = ((g 1) * (g 14) * (g 22)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0732_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323273321641200 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733 : SparsePolynomial.Poly := [([1,14,23], 1)]
theorem eval_atom0733 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0733 = ((g 1) * (g 14) * (g 23)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0733_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321024479252400 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734 : SparsePolynomial.Poly := [([1,15,15], 1)]
theorem eval_atom0734 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0734 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0734_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236349692006400 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0735 : SparsePolynomial.Poly := [([1,15,16], 1)]
theorem eval_atom0735 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0735 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0735_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402531313443840 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736 : SparsePolynomial.Poly := [([1,15,17], 1)]
theorem eval_atom0736 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (362157076915200 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737 : SparsePolynomial.Poly := [([1,15,18], 1)]
theorem eval_atom0737 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 1) * (g 15) * (g 18)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (408079884441600 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738 : SparsePolynomial.Poly := [([1,15,19], 1)]
theorem eval_atom0738 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 1) * (g 15) * (g 19)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352712728166400 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739 : SparsePolynomial.Poly := [([1,15,20], 1)]
theorem eval_atom0739 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 1) * (g 15) * (g 20)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444651124377600 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740 : SparsePolynomial.Poly := [([1,15,21], 1)]
theorem eval_atom0740 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 1) * (g 15) * (g 21)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (396881714073600 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741 : SparsePolynomial.Poly := [([1,15,22], 1)]
theorem eval_atom0741 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 1) * (g 15) * (g 22)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308523875923200 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742 : SparsePolynomial.Poly := [([1,15,23], 1)]
theorem eval_atom0742 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 1) * (g 15) * (g 23)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (301811953766400 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743 : SparsePolynomial.Poly := [([1,16,16], 1)]
theorem eval_atom0743 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218895236582400 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744 : SparsePolynomial.Poly := [([1,16,17], 1)]
theorem eval_atom0744 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (376667448729600 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745 : SparsePolynomial.Poly := [([1,16,18], 1)]
theorem eval_atom0745 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 1) * (g 16) * (g 18)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399373919078400 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746 : SparsePolynomial.Poly := [([1,16,19], 1)]
theorem eval_atom0746 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 1) * (g 16) * (g 19)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346047948288000 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747 : SparsePolynomial.Poly := [([1,16,20], 1)]
theorem eval_atom0747 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 1) * (g 16) * (g 20)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440027529984000 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748 : SparsePolynomial.Poly := [([1,16,21], 1)]
theorem eval_atom0748 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 1) * (g 16) * (g 21)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (394299305164800 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749 : SparsePolynomial.Poly := [([1,16,22], 1)]
theorem eval_atom0749 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 1) * (g 16) * (g 22)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (288457051008000 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750 : SparsePolynomial.Poly := [([1,16,23], 1)]
theorem eval_atom0750 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 1) * (g 16) * (g 23)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (322053709824000 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751 : SparsePolynomial.Poly := [([1,17,17], 1)]
theorem eval_atom0751 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210072006144000 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752 : SparsePolynomial.Poly := [([1,17,18], 1)]
theorem eval_atom0752 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 1) * (g 17) * (g 18)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410533430630400 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753 : SparsePolynomial.Poly := [([1,17,19], 1)]
theorem eval_atom0753 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 1) * (g 17) * (g 19)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (359248645324800 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754 : SparsePolynomial.Poly := [([1,17,20], 1)]
theorem eval_atom0754 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 1) * (g 17) * (g 20)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (455269412505600 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755 : SparsePolynomial.Poly := [([1,17,21], 1)]
theorem eval_atom0755 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 1) * (g 17) * (g 21)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411582373171200 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756 : SparsePolynomial.Poly := [([1,17,22], 1)]
theorem eval_atom0756 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 1) * (g 17) * (g 22)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (306657621580800 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757 : SparsePolynomial.Poly := [([1,17,23], 1)]
theorem eval_atom0757 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 1) * (g 17) * (g 23)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342295465881600 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758 : SparsePolynomial.Poly := [([1,18,18], 1)]
theorem eval_atom0758 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 1) * (g 18) * (g 18)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (240477164928000 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759 : SparsePolynomial.Poly := [([1,18,19], 1)]
theorem eval_atom0759 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 1) * (g 18) * (g 19)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (398116218931200 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760 : SparsePolynomial.Poly := [([1,18,20], 1)]
theorem eval_atom0760 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 1) * (g 18) * (g 20)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (529772682700800 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761 : SparsePolynomial.Poly := [([1,18,21], 1)]
theorem eval_atom0761 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 1) * (g 18) * (g 21)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (485943894374400 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762 : SparsePolynomial.Poly := [([1,18,22], 1)]
theorem eval_atom0762 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 1) * (g 18) * (g 22)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318619088793600 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763 : SparsePolynomial.Poly := [([1,18,23], 1)]
theorem eval_atom0763 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 1) * (g 18) * (g 23)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349384687344000 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764 : SparsePolynomial.Poly := [([1,19,19], 1)]
theorem eval_atom0764 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 1) * (g 19) * (g 19)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142023985044480 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765 : SparsePolynomial.Poly := [([1,19,20], 1)]
theorem eval_atom0765 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 1) * (g 19) * (g 20)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386251828300800 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766 : SparsePolynomial.Poly := [([1,19,21], 1)]
theorem eval_atom0766 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 1) * (g 19) * (g 21)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405395029670400 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 1) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767 : SparsePolynomial.Poly := [([1,19,22], 1)]
theorem eval_atom0767 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 1) * (g 19) * (g 22)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291706968806400 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 1) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768 : SparsePolynomial.Poly := [([1,19,23], 1)]
theorem eval_atom0768 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 1) * (g 19) * (g 23)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283733641699200 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 1) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block011 : SparsePolynomial.Poly := [([1,11,12], 394708547851200), ([1,11,13], 353450265078240), ([1,11,14], 321640443169056), ([1,11,15], 318715903738656), ([1,11,16], 299599119226656), ([1,11,17], 295381442401056), ([1,11,18], 349182426719808), ([1,11,19], 315381779675424), ([1,11,20], 369424182777408), ([1,11,21], 359408125596960), ([1,11,22], 330379014712320), ([1,11,23], 338126709026304), ([1,12,12], 242832577553280), ([1,12,13], 435085192840320), ([1,12,14], 385560346343040), ([1,12,15], 379386155583936), ([1,12,16], 357728520390336), ([1,12,17], 350969992883136), ([1,12,18], 415062219800448), ([1,12,19], 361270446634944), ([1,12,20], 439386346827648), ([1,12,21], 390978726874560), ([1,12,22], 325176814433280), ([1,12,23], 324378474292224), ([1,13,13], 241883189856000), ([1,13,14], 422611559979840), ([1,13,15], 385974487301760), ([1,13,16], 358553364624000), ([1,13,17], 348743690064000), ([1,13,18], 407775787372800), ([1,13,19], 355536072460800), ([1,13,20], 436182285369600), ([1,13,21], 384330504096000), ([1,13,22], 327597538800000), ([1,13,23], 327207015273600), ([1,14,14], 230358944692800), ([1,14,15], 415536541842240), ([1,14,16], 358531991415360), ([1,14,17], 344356141852800), ([1,14,18], 393140829312000), ([1,14,19], 345302980822800), ([1,14,20], 425629698278400), ([1,14,21], 375819102489600), ([1,14,22], 323273321641200), ([1,14,23], 321024479252400), ([1,15,15], 236349692006400), ([1,15,16], 402531313443840), ([1,15,17], 362157076915200), ([1,15,18], 408079884441600), ([1,15,19], 352712728166400), ([1,15,20], 444651124377600), ([1,15,21], 396881714073600), ([1,15,22], 308523875923200), ([1,15,23], 301811953766400), ([1,16,16], 218895236582400), ([1,16,17], 376667448729600), ([1,16,18], 399373919078400), ([1,16,19], 346047948288000), ([1,16,20], 440027529984000), ([1,16,21], 394299305164800), ([1,16,22], 288457051008000), ([1,16,23], 322053709824000), ([1,17,17], 210072006144000), ([1,17,18], 410533430630400), ([1,17,19], 359248645324800), ([1,17,20], 455269412505600), ([1,17,21], 411582373171200), ([1,17,22], 306657621580800), ([1,17,23], 342295465881600), ([1,18,18], 240477164928000), ([1,18,19], 398116218931200), ([1,18,20], 529772682700800), ([1,18,21], 485943894374400), ([1,18,22], 318619088793600), ([1,18,23], 349384687344000), ([1,19,19], 142023985044480), ([1,19,20], 386251828300800), ([1,19,21], 405395029670400), ([1,19,22], 291706968806400), ([1,19,23], 283733641699200)]
theorem block011_data : block011 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (394708547851200 : Int) atom0689) (SparsePolynomial.scale (353450265078240 : Int) atom0690)) (SparsePolynomial.merge (SparsePolynomial.scale (321640443169056 : Int) atom0691) (SparsePolynomial.merge (SparsePolynomial.scale (318715903738656 : Int) atom0692) (SparsePolynomial.scale (299599119226656 : Int) atom0693)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (295381442401056 : Int) atom0694) (SparsePolynomial.scale (349182426719808 : Int) atom0695)) (SparsePolynomial.merge (SparsePolynomial.scale (315381779675424 : Int) atom0696) (SparsePolynomial.merge (SparsePolynomial.scale (369424182777408 : Int) atom0697) (SparsePolynomial.scale (359408125596960 : Int) atom0698))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (330379014712320 : Int) atom0699) (SparsePolynomial.scale (338126709026304 : Int) atom0700)) (SparsePolynomial.merge (SparsePolynomial.scale (242832577553280 : Int) atom0701) (SparsePolynomial.merge (SparsePolynomial.scale (435085192840320 : Int) atom0702) (SparsePolynomial.scale (385560346343040 : Int) atom0703)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (379386155583936 : Int) atom0704) (SparsePolynomial.scale (357728520390336 : Int) atom0705)) (SparsePolynomial.merge (SparsePolynomial.scale (350969992883136 : Int) atom0706) (SparsePolynomial.merge (SparsePolynomial.scale (415062219800448 : Int) atom0707) (SparsePolynomial.scale (361270446634944 : Int) atom0708)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (439386346827648 : Int) atom0709) (SparsePolynomial.scale (390978726874560 : Int) atom0710)) (SparsePolynomial.merge (SparsePolynomial.scale (325176814433280 : Int) atom0711) (SparsePolynomial.merge (SparsePolynomial.scale (324378474292224 : Int) atom0712) (SparsePolynomial.scale (241883189856000 : Int) atom0713)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (422611559979840 : Int) atom0714) (SparsePolynomial.scale (385974487301760 : Int) atom0715)) (SparsePolynomial.merge (SparsePolynomial.scale (358553364624000 : Int) atom0716) (SparsePolynomial.merge (SparsePolynomial.scale (348743690064000 : Int) atom0717) (SparsePolynomial.scale (407775787372800 : Int) atom0718))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (355536072460800 : Int) atom0719) (SparsePolynomial.scale (436182285369600 : Int) atom0720)) (SparsePolynomial.merge (SparsePolynomial.scale (384330504096000 : Int) atom0721) (SparsePolynomial.merge (SparsePolynomial.scale (327597538800000 : Int) atom0722) (SparsePolynomial.scale (327207015273600 : Int) atom0723)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (230358944692800 : Int) atom0724) (SparsePolynomial.scale (415536541842240 : Int) atom0725)) (SparsePolynomial.merge (SparsePolynomial.scale (358531991415360 : Int) atom0726) (SparsePolynomial.merge (SparsePolynomial.scale (344356141852800 : Int) atom0727) (SparsePolynomial.scale (393140829312000 : Int) atom0728))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (345302980822800 : Int) atom0729) (SparsePolynomial.scale (425629698278400 : Int) atom0730)) (SparsePolynomial.merge (SparsePolynomial.scale (375819102489600 : Int) atom0731) (SparsePolynomial.merge (SparsePolynomial.scale (323273321641200 : Int) atom0732) (SparsePolynomial.scale (321024479252400 : Int) atom0733)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (236349692006400 : Int) atom0734) (SparsePolynomial.scale (402531313443840 : Int) atom0735)) (SparsePolynomial.merge (SparsePolynomial.scale (362157076915200 : Int) atom0736) (SparsePolynomial.merge (SparsePolynomial.scale (408079884441600 : Int) atom0737) (SparsePolynomial.scale (352712728166400 : Int) atom0738))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (444651124377600 : Int) atom0739) (SparsePolynomial.scale (396881714073600 : Int) atom0740)) (SparsePolynomial.merge (SparsePolynomial.scale (308523875923200 : Int) atom0741) (SparsePolynomial.merge (SparsePolynomial.scale (301811953766400 : Int) atom0742) (SparsePolynomial.scale (218895236582400 : Int) atom0743)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (376667448729600 : Int) atom0744) (SparsePolynomial.scale (399373919078400 : Int) atom0745)) (SparsePolynomial.merge (SparsePolynomial.scale (346047948288000 : Int) atom0746) (SparsePolynomial.merge (SparsePolynomial.scale (440027529984000 : Int) atom0747) (SparsePolynomial.scale (394299305164800 : Int) atom0748)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (288457051008000 : Int) atom0749) (SparsePolynomial.scale (322053709824000 : Int) atom0750)) (SparsePolynomial.merge (SparsePolynomial.scale (210072006144000 : Int) atom0751) (SparsePolynomial.merge (SparsePolynomial.scale (410533430630400 : Int) atom0752) (SparsePolynomial.scale (359248645324800 : Int) atom0753)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (455269412505600 : Int) atom0754) (SparsePolynomial.scale (411582373171200 : Int) atom0755)) (SparsePolynomial.merge (SparsePolynomial.scale (306657621580800 : Int) atom0756) (SparsePolynomial.merge (SparsePolynomial.scale (342295465881600 : Int) atom0757) (SparsePolynomial.scale (240477164928000 : Int) atom0758))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (398116218931200 : Int) atom0759) (SparsePolynomial.scale (529772682700800 : Int) atom0760)) (SparsePolynomial.merge (SparsePolynomial.scale (485943894374400 : Int) atom0761) (SparsePolynomial.merge (SparsePolynomial.scale (318619088793600 : Int) atom0762) (SparsePolynomial.scale (349384687344000 : Int) atom0763)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142023985044480 : Int) atom0764) (SparsePolynomial.scale (386251828300800 : Int) atom0765)) (SparsePolynomial.merge (SparsePolynomial.scale (405395029670400 : Int) atom0766) (SparsePolynomial.merge (SparsePolynomial.scale (291706968806400 : Int) atom0767) (SparsePolynomial.scale (283733641699200 : Int) atom0768)))))))) := by decide +kernel
theorem block011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block011 := by
  rw [block011_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0689_nonneg g hg hA hB) (atom0690_nonneg g hg hA hB)) (add_nonneg (atom0691_nonneg g hg hA hB) (add_nonneg (atom0692_nonneg g hg hA hB) (atom0693_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0694_nonneg g hg hA hB) (atom0695_nonneg g hg hA hB)) (add_nonneg (atom0696_nonneg g hg hA hB) (add_nonneg (atom0697_nonneg g hg hA hB) (atom0698_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0699_nonneg g hg hA hB) (atom0700_nonneg g hg hA hB)) (add_nonneg (atom0701_nonneg g hg hA hB) (add_nonneg (atom0702_nonneg g hg hA hB) (atom0703_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0704_nonneg g hg hA hB) (atom0705_nonneg g hg hA hB)) (add_nonneg (atom0706_nonneg g hg hA hB) (add_nonneg (atom0707_nonneg g hg hA hB) (atom0708_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0709_nonneg g hg hA hB) (atom0710_nonneg g hg hA hB)) (add_nonneg (atom0711_nonneg g hg hA hB) (add_nonneg (atom0712_nonneg g hg hA hB) (atom0713_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0714_nonneg g hg hA hB) (atom0715_nonneg g hg hA hB)) (add_nonneg (atom0716_nonneg g hg hA hB) (add_nonneg (atom0717_nonneg g hg hA hB) (atom0718_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0719_nonneg g hg hA hB) (atom0720_nonneg g hg hA hB)) (add_nonneg (atom0721_nonneg g hg hA hB) (add_nonneg (atom0722_nonneg g hg hA hB) (atom0723_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0724_nonneg g hg hA hB) (atom0725_nonneg g hg hA hB)) (add_nonneg (atom0726_nonneg g hg hA hB) (add_nonneg (atom0727_nonneg g hg hA hB) (atom0728_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0729_nonneg g hg hA hB) (atom0730_nonneg g hg hA hB)) (add_nonneg (atom0731_nonneg g hg hA hB) (add_nonneg (atom0732_nonneg g hg hA hB) (atom0733_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0734_nonneg g hg hA hB) (atom0735_nonneg g hg hA hB)) (add_nonneg (atom0736_nonneg g hg hA hB) (add_nonneg (atom0737_nonneg g hg hA hB) (atom0738_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0739_nonneg g hg hA hB) (atom0740_nonneg g hg hA hB)) (add_nonneg (atom0741_nonneg g hg hA hB) (add_nonneg (atom0742_nonneg g hg hA hB) (atom0743_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0744_nonneg g hg hA hB) (atom0745_nonneg g hg hA hB)) (add_nonneg (atom0746_nonneg g hg hA hB) (add_nonneg (atom0747_nonneg g hg hA hB) (atom0748_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0749_nonneg g hg hA hB) (atom0750_nonneg g hg hA hB)) (add_nonneg (atom0751_nonneg g hg hA hB) (add_nonneg (atom0752_nonneg g hg hA hB) (atom0753_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0754_nonneg g hg hA hB) (atom0755_nonneg g hg hA hB)) (add_nonneg (atom0756_nonneg g hg hA hB) (add_nonneg (atom0757_nonneg g hg hA hB) (atom0758_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0759_nonneg g hg hA hB) (atom0760_nonneg g hg hA hB)) (add_nonneg (atom0761_nonneg g hg hA hB) (add_nonneg (atom0762_nonneg g hg hA hB) (atom0763_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0764_nonneg g hg hA hB) (atom0765_nonneg g hg hA hB)) (add_nonneg (atom0766_nonneg g hg hA hB) (add_nonneg (atom0767_nonneg g hg hA hB) (atom0768_nonneg g hg hA hB))))))))

end APPT.Finite24
