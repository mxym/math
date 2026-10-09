import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1696 : SparsePolynomial.Poly := [([14,15,17], 1)]
theorem eval_atom1696 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1696 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom1696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1696_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49533129676800 : Int) atom1696) := by
  rw [SparsePolynomial.eval_scale, eval_atom1696]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1697 : SparsePolynomial.Poly := [([14,15,18], 1)]
theorem eval_atom1697 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1697 = ((g 14) * (g 15) * (g 18)) := by
  norm_num [atom1697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1697_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59532643699200 : Int) atom1697) := by
  rw [SparsePolynomial.eval_scale, eval_atom1697]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1698 : SparsePolynomial.Poly := [([14,15,19], 1)]
theorem eval_atom1698 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1698 = ((g 14) * (g 15) * (g 19)) := by
  norm_num [atom1698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1698_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43553022105600 : Int) atom1698) := by
  rw [SparsePolynomial.eval_scale, eval_atom1698]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1699 : SparsePolynomial.Poly := [([14,15,20], 1)]
theorem eval_atom1699 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1699 = ((g 14) * (g 15) * (g 20)) := by
  norm_num [atom1699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1699_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85602216268800 : Int) atom1699) := by
  rw [SparsePolynomial.eval_scale, eval_atom1699]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1700 : SparsePolynomial.Poly := [([14,16,16], 1)]
theorem eval_atom1700 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1700 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom1700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1700_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4836604469760 : Int) atom1700) := by
  rw [SparsePolynomial.eval_scale, eval_atom1700]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1701 : SparsePolynomial.Poly := [([14,16,17], 1)]
theorem eval_atom1701 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1701 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom1701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1701_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47815814592000 : Int) atom1701) := by
  rw [SparsePolynomial.eval_scale, eval_atom1701]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1702 : SparsePolynomial.Poly := [([14,16,18], 1)]
theorem eval_atom1702 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1702 = ((g 14) * (g 16) * (g 18)) := by
  norm_num [atom1702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1702_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68387445504000 : Int) atom1702) := by
  rw [SparsePolynomial.eval_scale, eval_atom1702]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1703 : SparsePolynomial.Poly := [([14,16,19], 1)]
theorem eval_atom1703 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1703 = ((g 14) * (g 16) * (g 19)) := by
  norm_num [atom1703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1703_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63497105280000 : Int) atom1703) := by
  rw [SparsePolynomial.eval_scale, eval_atom1703]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1704 : SparsePolynomial.Poly := [([14,16,20], 1)]
theorem eval_atom1704 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1704 = ((g 14) * (g 16) * (g 20)) := by
  norm_num [atom1704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1704_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91041511680000 : Int) atom1704) := by
  rw [SparsePolynomial.eval_scale, eval_atom1704]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1705 : SparsePolynomial.Poly := [([14,17,17], 1)]
theorem eval_atom1705 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1705 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom1705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1705_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39020933952000 : Int) atom1705) := by
  rw [SparsePolynomial.eval_scale, eval_atom1705]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1706 : SparsePolynomial.Poly := [([14,17,18], 1)]
theorem eval_atom1706 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1706 = ((g 14) * (g 17) * (g 18)) := by
  norm_num [atom1706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1706_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84087448704000 : Int) atom1706) := by
  rw [SparsePolynomial.eval_scale, eval_atom1706]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1707 : SparsePolynomial.Poly := [([14,17,19], 1)]
theorem eval_atom1707 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1707 = ((g 14) * (g 17) * (g 19)) := by
  norm_num [atom1707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1707_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82236760704000 : Int) atom1707) := by
  rw [SparsePolynomial.eval_scale, eval_atom1707]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1708 : SparsePolynomial.Poly := [([14,17,20], 1)]
theorem eval_atom1708 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1708 = ((g 14) * (g 17) * (g 20)) := by
  norm_num [atom1708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1708_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98579775168000 : Int) atom1708) := by
  rw [SparsePolynomial.eval_scale, eval_atom1708]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1709 : SparsePolynomial.Poly := [([14,18,18], 1)]
theorem eval_atom1709 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1709 = ((g 14) * (g 18) * (g 18)) := by
  norm_num [atom1709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1709_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38658816000000 : Int) atom1709) := by
  rw [SparsePolynomial.eval_scale, eval_atom1709]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1710 : SparsePolynomial.Poly := [([14,18,19], 1)]
theorem eval_atom1710 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1710 = ((g 14) * (g 18) * (g 19)) := by
  norm_num [atom1710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1710_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85996536192000 : Int) atom1710) := by
  rw [SparsePolynomial.eval_scale, eval_atom1710]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1711 : SparsePolynomial.Poly := [([14,18,20], 1)]
theorem eval_atom1711 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1711 = ((g 14) * (g 18) * (g 20)) := by
  norm_num [atom1711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1711_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104862038400000 : Int) atom1711) := by
  rw [SparsePolynomial.eval_scale, eval_atom1711]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1712 : SparsePolynomial.Poly := [([14,19,19], 1)]
theorem eval_atom1712 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1712 = ((g 14) * (g 19) * (g 19)) := by
  norm_num [atom1712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1712_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44360991360000 : Int) atom1712) := by
  rw [SparsePolynomial.eval_scale, eval_atom1712]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1713 : SparsePolynomial.Poly := [([14,19,20], 1)]
theorem eval_atom1713 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1713 = ((g 14) * (g 19) * (g 20)) := by
  norm_num [atom1713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1713_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110109972672000 : Int) atom1713) := by
  rw [SparsePolynomial.eval_scale, eval_atom1713]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1714 : SparsePolynomial.Poly := [([14,20,20], 1)]
theorem eval_atom1714 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1714 = ((g 14) * (g 20) * (g 20)) := by
  norm_num [atom1714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1714_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59341282560000 : Int) atom1714) := by
  rw [SparsePolynomial.eval_scale, eval_atom1714]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1715 : SparsePolynomial.Poly := [([15,15,15], 1)]
theorem eval_atom1715 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1715 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom1715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1715_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (966470400000 : Int) atom1715) := by
  rw [SparsePolynomial.eval_scale, eval_atom1715]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1716 : SparsePolynomial.Poly := [([15,15,16], 1)]
theorem eval_atom1716 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1716 = ((g 15) * (g 15) * (g 16)) := by
  norm_num [atom1716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1716_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7720165555200 : Int) atom1716) := by
  rw [SparsePolynomial.eval_scale, eval_atom1716]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1717 : SparsePolynomial.Poly := [([15,15,17], 1)]
theorem eval_atom1717 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1717 = ((g 15) * (g 15) * (g 17)) := by
  norm_num [atom1717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1717_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28555128806400 : Int) atom1717) := by
  rw [SparsePolynomial.eval_scale, eval_atom1717]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1718 : SparsePolynomial.Poly := [([15,15,18], 1)]
theorem eval_atom1718 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1718 = ((g 15) * (g 15) * (g 18)) := by
  norm_num [atom1718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1718_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34410212121600 : Int) atom1718) := by
  rw [SparsePolynomial.eval_scale, eval_atom1718]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1719 : SparsePolynomial.Poly := [([15,15,19], 1)]
theorem eval_atom1719 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1719 = ((g 15) * (g 15) * (g 19)) := by
  norm_num [atom1719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1719_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22182428620800 : Int) atom1719) := by
  rw [SparsePolynomial.eval_scale, eval_atom1719]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1720 : SparsePolynomial.Poly := [([15,15,20], 1)]
theorem eval_atom1720 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1720 = ((g 15) * (g 15) * (g 20)) := by
  norm_num [atom1720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1720_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44051720832000 : Int) atom1720) := by
  rw [SparsePolynomial.eval_scale, eval_atom1720]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1721 : SparsePolynomial.Poly := [([15,16,16], 1)]
theorem eval_atom1721 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1721 = ((g 15) * (g 16) * (g 16)) := by
  norm_num [atom1721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1721_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7849286000640 : Int) atom1721) := by
  rw [SparsePolynomial.eval_scale, eval_atom1721]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1722 : SparsePolynomial.Poly := [([15,16,17], 1)]
theorem eval_atom1722 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1722 = ((g 15) * (g 16) * (g 17)) := by
  norm_num [atom1722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1722_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56289827059200 : Int) atom1722) := by
  rw [SparsePolynomial.eval_scale, eval_atom1722]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1723 : SparsePolynomial.Poly := [([15,16,18], 1)]
theorem eval_atom1723 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1723 = ((g 15) * (g 16) * (g 18)) := by
  norm_num [atom1723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1723_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78697751731200 : Int) atom1723) := by
  rw [SparsePolynomial.eval_scale, eval_atom1723]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1724 : SparsePolynomial.Poly := [([15,16,19], 1)]
theorem eval_atom1724 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1724 = ((g 15) * (g 16) * (g 19)) := by
  norm_num [atom1724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1724_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65457107251200 : Int) atom1724) := by
  rw [SparsePolynomial.eval_scale, eval_atom1724]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1725 : SparsePolynomial.Poly := [([15,16,20], 1)]
theorem eval_atom1725 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1725 = ((g 15) * (g 16) * (g 20)) := by
  norm_num [atom1725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1725_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94837807411200 : Int) atom1725) := by
  rw [SparsePolynomial.eval_scale, eval_atom1725]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1726 : SparsePolynomial.Poly := [([15,17,17], 1)]
theorem eval_atom1726 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1726 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom1726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1726_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43748907148800 : Int) atom1726) := by
  rw [SparsePolynomial.eval_scale, eval_atom1726]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1727 : SparsePolynomial.Poly := [([15,17,18], 1)]
theorem eval_atom1727 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1727 = ((g 15) * (g 17) * (g 18)) := by
  norm_num [atom1727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1727_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95547854707200 : Int) atom1727) := by
  rw [SparsePolynomial.eval_scale, eval_atom1727]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1728 : SparsePolynomial.Poly := [([15,17,19], 1)]
theorem eval_atom1728 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1728 = ((g 15) * (g 17) * (g 19)) := by
  norm_num [atom1728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1728_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85515028300800 : Int) atom1728) := by
  rw [SparsePolynomial.eval_scale, eval_atom1728]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1729 : SparsePolynomial.Poly := [([15,17,20], 1)]
theorem eval_atom1729 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1729 = ((g 15) * (g 17) * (g 20)) := by
  norm_num [atom1729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1729_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85557964262400 : Int) atom1729) := by
  rw [SparsePolynomial.eval_scale, eval_atom1729]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1730 : SparsePolynomial.Poly := [([15,18,18], 1)]
theorem eval_atom1730 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1730 = ((g 15) * (g 18) * (g 18)) := by
  norm_num [atom1730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1730_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44964068889600 : Int) atom1730) := by
  rw [SparsePolynomial.eval_scale, eval_atom1730]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1731 : SparsePolynomial.Poly := [([15,18,19], 1)]
theorem eval_atom1731 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1731 = ((g 15) * (g 18) * (g 19)) := by
  norm_num [atom1731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1731_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90593069414400 : Int) atom1731) := by
  rw [SparsePolynomial.eval_scale, eval_atom1731]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1732 : SparsePolynomial.Poly := [([15,18,20], 1)]
theorem eval_atom1732 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1732 = ((g 15) * (g 18) * (g 20)) := by
  norm_num [atom1732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1732_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91258001049600 : Int) atom1732) := by
  rw [SparsePolynomial.eval_scale, eval_atom1732]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1733 : SparsePolynomial.Poly := [([15,19,19], 1)]
theorem eval_atom1733 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1733 = ((g 15) * (g 19) * (g 19)) := by
  norm_num [atom1733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1733_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47318390784000 : Int) atom1733) := by
  rw [SparsePolynomial.eval_scale, eval_atom1733]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1734 : SparsePolynomial.Poly := [([15,19,20], 1)]
theorem eval_atom1734 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1734 = ((g 15) * (g 19) * (g 20)) := by
  norm_num [atom1734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1734_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97992366796800 : Int) atom1734) := by
  rw [SparsePolynomial.eval_scale, eval_atom1734]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1735 : SparsePolynomial.Poly := [([15,20,20], 1)]
theorem eval_atom1735 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1735 = ((g 15) * (g 20) * (g 20)) := by
  norm_num [atom1735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1735_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43839097344000 : Int) atom1735) := by
  rw [SparsePolynomial.eval_scale, eval_atom1735]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1736 : SparsePolynomial.Poly := [([16,16,17], 1)]
theorem eval_atom1736 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1736 = ((g 16) * (g 16) * (g 17)) := by
  norm_num [atom1736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1736_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19329111889920 : Int) atom1736) := by
  rw [SparsePolynomial.eval_scale, eval_atom1736]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1737 : SparsePolynomial.Poly := [([16,16,18], 1)]
theorem eval_atom1737 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1737 = ((g 16) * (g 16) * (g 18)) := by
  norm_num [atom1737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1737_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34842417684480 : Int) atom1737) := by
  rw [SparsePolynomial.eval_scale, eval_atom1737]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1738 : SparsePolynomial.Poly := [([16,16,19], 1)]
theorem eval_atom1738 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1738 = ((g 16) * (g 16) * (g 19)) := by
  norm_num [atom1738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1738_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32177665497600 : Int) atom1738) := by
  rw [SparsePolynomial.eval_scale, eval_atom1738]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1739 : SparsePolynomial.Poly := [([16,16,20], 1)]
theorem eval_atom1739 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1739 = ((g 16) * (g 16) * (g 20)) := by
  norm_num [atom1739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1739_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46561451166720 : Int) atom1739) := by
  rw [SparsePolynomial.eval_scale, eval_atom1739]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1740 : SparsePolynomial.Poly := [([16,17,17], 1)]
theorem eval_atom1740 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1740 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom1740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1740_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35376476889600 : Int) atom1740) := by
  rw [SparsePolynomial.eval_scale, eval_atom1740]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1741 : SparsePolynomial.Poly := [([16,17,18], 1)]
theorem eval_atom1741 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1741 = ((g 16) * (g 17) * (g 18)) := by
  norm_num [atom1741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1741_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88814558246400 : Int) atom1741) := by
  rw [SparsePolynomial.eval_scale, eval_atom1741]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1742 : SparsePolynomial.Poly := [([16,17,19], 1)]
theorem eval_atom1742 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1742 = ((g 16) * (g 17) * (g 19)) := by
  norm_num [atom1742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1742_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88793295897600 : Int) atom1742) := by
  rw [SparsePolynomial.eval_scale, eval_atom1742]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1743 : SparsePolynomial.Poly := [([16,17,20], 1)]
theorem eval_atom1743 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1743 = ((g 16) * (g 17) * (g 20)) := by
  norm_num [atom1743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1743_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90840691468800 : Int) atom1743) := by
  rw [SparsePolynomial.eval_scale, eval_atom1743]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1744 : SparsePolynomial.Poly := [([16,18,18], 1)]
theorem eval_atom1744 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1744 = ((g 16) * (g 18) * (g 18)) := by
  norm_num [atom1744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1744_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46176022771200 : Int) atom1744) := by
  rw [SparsePolynomial.eval_scale, eval_atom1744]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1745 : SparsePolynomial.Poly := [([16,18,19], 1)]
theorem eval_atom1745 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1745 = ((g 16) * (g 18) * (g 19)) := by
  norm_num [atom1745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1745_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95189602636800 : Int) atom1745) := by
  rw [SparsePolynomial.eval_scale, eval_atom1745]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1746 : SparsePolynomial.Poly := [([16,18,20], 1)]
theorem eval_atom1746 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1746 = ((g 16) * (g 18) * (g 20)) := by
  norm_num [atom1746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1746_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98027159731200 : Int) atom1746) := by
  rw [SparsePolynomial.eval_scale, eval_atom1746]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1747 : SparsePolynomial.Poly := [([16,19,19], 1)]
theorem eval_atom1747 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1747 = ((g 16) * (g 19) * (g 19)) := by
  norm_num [atom1747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1747_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50275790208000 : Int) atom1747) := by
  rw [SparsePolynomial.eval_scale, eval_atom1747]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1748 : SparsePolynomial.Poly := [([16,19,20], 1)]
theorem eval_atom1748 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1748 = ((g 16) * (g 19) * (g 20)) := by
  norm_num [atom1748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1748_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106247956953600 : Int) atom1748) := by
  rw [SparsePolynomial.eval_scale, eval_atom1748]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1749 : SparsePolynomial.Poly := [([16,20,20], 1)]
theorem eval_atom1749 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1749 = ((g 16) * (g 20) * (g 20)) := by
  norm_num [atom1749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1749_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48710108160000 : Int) atom1749) := by
  rw [SparsePolynomial.eval_scale, eval_atom1749]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1750 : SparsePolynomial.Poly := [([17,17,17], 1)]
theorem eval_atom1750 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1750 = ((g 17) * (g 17) * (g 17)) := by
  norm_num [atom1750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1750_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14339418508800 : Int) atom1750) := by
  rw [SparsePolynomial.eval_scale, eval_atom1750]
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 17) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1751 : SparsePolynomial.Poly := [([17,17,18], 1)]
theorem eval_atom1751 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1751 = ((g 17) * (g 17) * (g 18)) := by
  norm_num [atom1751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1751_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45044183116800 : Int) atom1751) := by
  rw [SparsePolynomial.eval_scale, eval_atom1751]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1752 : SparsePolynomial.Poly := [([17,17,19], 1)]
theorem eval_atom1752 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1752 = ((g 17) * (g 17) * (g 19)) := by
  norm_num [atom1752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1752_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46035781747200 : Int) atom1752) := by
  rw [SparsePolynomial.eval_scale, eval_atom1752]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1753 : SparsePolynomial.Poly := [([17,17,20], 1)]
theorem eval_atom1753 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1753 = ((g 17) * (g 17) * (g 20)) := by
  norm_num [atom1753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1753_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32047500441600 : Int) atom1753) := by
  rw [SparsePolynomial.eval_scale, eval_atom1753]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1754 : SparsePolynomial.Poly := [([17,18,18], 1)]
theorem eval_atom1754 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1754 = ((g 17) * (g 18) * (g 18)) := by
  norm_num [atom1754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1754_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47387976652800 : Int) atom1754) := by
  rw [SparsePolynomial.eval_scale, eval_atom1754]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1755 : SparsePolynomial.Poly := [([17,18,19], 1)]
theorem eval_atom1755 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1755 = ((g 17) * (g 18) * (g 19)) := by
  norm_num [atom1755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1755_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99786135859200 : Int) atom1755) := by
  rw [SparsePolynomial.eval_scale, eval_atom1755]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1756 : SparsePolynomial.Poly := [([17,18,20], 1)]
theorem eval_atom1756 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1756 = ((g 17) * (g 18) * (g 20)) := by
  norm_num [atom1756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1756_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72767900620800 : Int) atom1756) := by
  rw [SparsePolynomial.eval_scale, eval_atom1756]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1757 : SparsePolynomial.Poly := [([17,19,19], 1)]
theorem eval_atom1757 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1757 = ((g 17) * (g 19) * (g 19)) := by
  norm_num [atom1757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1757_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53233189632000 : Int) atom1757) := by
  rw [SparsePolynomial.eval_scale, eval_atom1757]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1758 : SparsePolynomial.Poly := [([17,19,20], 1)]
theorem eval_atom1758 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1758 = ((g 17) * (g 19) * (g 20)) := by
  norm_num [atom1758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1758_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82475129318400 : Int) atom1758) := by
  rw [SparsePolynomial.eval_scale, eval_atom1758]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1759 : SparsePolynomial.Poly := [([17,20,20], 1)]
theorem eval_atom1759 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1759 = ((g 17) * (g 20) * (g 20)) := by
  norm_num [atom1759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1759_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21552701184000 : Int) atom1759) := by
  rw [SparsePolynomial.eval_scale, eval_atom1759]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1760 : SparsePolynomial.Poly := [([18,18,18], 1)]
theorem eval_atom1760 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1760 = ((g 18) * (g 18) * (g 18)) := by
  norm_num [atom1760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1760_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16199976844800 : Int) atom1760) := by
  rw [SparsePolynomial.eval_scale, eval_atom1760]
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 18) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1761 : SparsePolynomial.Poly := [([18,18,19], 1)]
theorem eval_atom1761 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1761 = ((g 18) * (g 18) * (g 19)) := by
  norm_num [atom1761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1761_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52191334540800 : Int) atom1761) := by
  rw [SparsePolynomial.eval_scale, eval_atom1761]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1762 : SparsePolynomial.Poly := [([18,18,20], 1)]
theorem eval_atom1762 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1762 = ((g 18) * (g 18) * (g 20)) := by
  norm_num [atom1762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1762_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38734200691200 : Int) atom1762) := by
  rw [SparsePolynomial.eval_scale, eval_atom1762]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1763 : SparsePolynomial.Poly := [([18,19,19], 1)]
theorem eval_atom1763 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1763 = ((g 18) * (g 19) * (g 19)) := by
  norm_num [atom1763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1763_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56190589056000 : Int) atom1763) := by
  rw [SparsePolynomial.eval_scale, eval_atom1763]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1764 : SparsePolynomial.Poly := [([18,19,20], 1)]
theorem eval_atom1764 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1764 = ((g 18) * (g 19) * (g 20)) := by
  norm_num [atom1764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1764_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88662061555200 : Int) atom1764) := by
  rw [SparsePolynomial.eval_scale, eval_atom1764]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1765 : SparsePolynomial.Poly := [([18,20,20], 1)]
theorem eval_atom1765 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1765 = ((g 18) * (g 20) * (g 20)) := by
  norm_num [atom1765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1765_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24355054080000 : Int) atom1765) := by
  rw [SparsePolynomial.eval_scale, eval_atom1765]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1766 : SparsePolynomial.Poly := [([19,19,19], 1)]
theorem eval_atom1766 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1766 = ((g 19) * (g 19) * (g 19)) := by
  norm_num [atom1766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1766_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19715996160000 : Int) atom1766) := by
  rw [SparsePolynomial.eval_scale, eval_atom1766]
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 19) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1767 : SparsePolynomial.Poly := [([19,19,20], 1)]
theorem eval_atom1767 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1767 = ((g 19) * (g 19) * (g 20)) := by
  norm_num [atom1767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1767_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48458825856000 : Int) atom1767) := by
  rw [SparsePolynomial.eval_scale, eval_atom1767]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1768 : SparsePolynomial.Poly := [([19,20,20], 1)]
theorem eval_atom1768 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1768 = ((g 19) * (g 20) * (g 20)) := by
  norm_num [atom1768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1768_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29226064896000 : Int) atom1768) := by
  rw [SparsePolynomial.eval_scale, eval_atom1768]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block023 : SparsePolynomial.Poly := [([14,15,17], 49533129676800), ([14,15,18], 59532643699200), ([14,15,19], 43553022105600), ([14,15,20], 85602216268800), ([14,16,16], 4836604469760), ([14,16,17], 47815814592000), ([14,16,18], 68387445504000), ([14,16,19], 63497105280000), ([14,16,20], 91041511680000), ([14,17,17], 39020933952000), ([14,17,18], 84087448704000), ([14,17,19], 82236760704000), ([14,17,20], 98579775168000), ([14,18,18], 38658816000000), ([14,18,19], 85996536192000), ([14,18,20], 104862038400000), ([14,19,19], 44360991360000), ([14,19,20], 110109972672000), ([14,20,20], 59341282560000), ([15,15,15], 966470400000), ([15,15,16], 7720165555200), ([15,15,17], 28555128806400), ([15,15,18], 34410212121600), ([15,15,19], 22182428620800), ([15,15,20], 44051720832000), ([15,16,16], 7849286000640), ([15,16,17], 56289827059200), ([15,16,18], 78697751731200), ([15,16,19], 65457107251200), ([15,16,20], 94837807411200), ([15,17,17], 43748907148800), ([15,17,18], 95547854707200), ([15,17,19], 85515028300800), ([15,17,20], 85557964262400), ([15,18,18], 44964068889600), ([15,18,19], 90593069414400), ([15,18,20], 91258001049600), ([15,19,19], 47318390784000), ([15,19,20], 97992366796800), ([15,20,20], 43839097344000), ([16,16,17], 19329111889920), ([16,16,18], 34842417684480), ([16,16,19], 32177665497600), ([16,16,20], 46561451166720), ([16,17,17], 35376476889600), ([16,17,18], 88814558246400), ([16,17,19], 88793295897600), ([16,17,20], 90840691468800), ([16,18,18], 46176022771200), ([16,18,19], 95189602636800), ([16,18,20], 98027159731200), ([16,19,19], 50275790208000), ([16,19,20], 106247956953600), ([16,20,20], 48710108160000), ([17,17,17], 14339418508800), ([17,17,18], 45044183116800), ([17,17,19], 46035781747200), ([17,17,20], 32047500441600), ([17,18,18], 47387976652800), ([17,18,19], 99786135859200), ([17,18,20], 72767900620800), ([17,19,19], 53233189632000), ([17,19,20], 82475129318400), ([17,20,20], 21552701184000), ([18,18,18], 16199976844800), ([18,18,19], 52191334540800), ([18,18,20], 38734200691200), ([18,19,19], 56190589056000), ([18,19,20], 88662061555200), ([18,20,20], 24355054080000), ([19,19,19], 19715996160000), ([19,19,20], 48458825856000), ([19,20,20], 29226064896000)]
theorem block023_data : block023 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49533129676800 : Int) atom1696) (SparsePolynomial.scale (59532643699200 : Int) atom1697)) (SparsePolynomial.merge (SparsePolynomial.scale (43553022105600 : Int) atom1698) (SparsePolynomial.scale (85602216268800 : Int) atom1699))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4836604469760 : Int) atom1700) (SparsePolynomial.scale (47815814592000 : Int) atom1701)) (SparsePolynomial.merge (SparsePolynomial.scale (68387445504000 : Int) atom1702) (SparsePolynomial.merge (SparsePolynomial.scale (63497105280000 : Int) atom1703) (SparsePolynomial.scale (91041511680000 : Int) atom1704))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39020933952000 : Int) atom1705) (SparsePolynomial.scale (84087448704000 : Int) atom1706)) (SparsePolynomial.merge (SparsePolynomial.scale (82236760704000 : Int) atom1707) (SparsePolynomial.scale (98579775168000 : Int) atom1708))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38658816000000 : Int) atom1709) (SparsePolynomial.scale (85996536192000 : Int) atom1710)) (SparsePolynomial.merge (SparsePolynomial.scale (104862038400000 : Int) atom1711) (SparsePolynomial.merge (SparsePolynomial.scale (44360991360000 : Int) atom1712) (SparsePolynomial.scale (110109972672000 : Int) atom1713)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (59341282560000 : Int) atom1714) (SparsePolynomial.scale (966470400000 : Int) atom1715)) (SparsePolynomial.merge (SparsePolynomial.scale (7720165555200 : Int) atom1716) (SparsePolynomial.scale (28555128806400 : Int) atom1717))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34410212121600 : Int) atom1718) (SparsePolynomial.scale (22182428620800 : Int) atom1719)) (SparsePolynomial.merge (SparsePolynomial.scale (44051720832000 : Int) atom1720) (SparsePolynomial.merge (SparsePolynomial.scale (7849286000640 : Int) atom1721) (SparsePolynomial.scale (56289827059200 : Int) atom1722))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (78697751731200 : Int) atom1723) (SparsePolynomial.scale (65457107251200 : Int) atom1724)) (SparsePolynomial.merge (SparsePolynomial.scale (94837807411200 : Int) atom1725) (SparsePolynomial.scale (43748907148800 : Int) atom1726))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (95547854707200 : Int) atom1727) (SparsePolynomial.scale (85515028300800 : Int) atom1728)) (SparsePolynomial.merge (SparsePolynomial.scale (85557964262400 : Int) atom1729) (SparsePolynomial.merge (SparsePolynomial.scale (44964068889600 : Int) atom1730) (SparsePolynomial.scale (90593069414400 : Int) atom1731))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (91258001049600 : Int) atom1732) (SparsePolynomial.scale (47318390784000 : Int) atom1733)) (SparsePolynomial.merge (SparsePolynomial.scale (97992366796800 : Int) atom1734) (SparsePolynomial.scale (43839097344000 : Int) atom1735))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19329111889920 : Int) atom1736) (SparsePolynomial.scale (34842417684480 : Int) atom1737)) (SparsePolynomial.merge (SparsePolynomial.scale (32177665497600 : Int) atom1738) (SparsePolynomial.merge (SparsePolynomial.scale (46561451166720 : Int) atom1739) (SparsePolynomial.scale (35376476889600 : Int) atom1740))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88814558246400 : Int) atom1741) (SparsePolynomial.scale (88793295897600 : Int) atom1742)) (SparsePolynomial.merge (SparsePolynomial.scale (90840691468800 : Int) atom1743) (SparsePolynomial.scale (46176022771200 : Int) atom1744))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (95189602636800 : Int) atom1745) (SparsePolynomial.scale (98027159731200 : Int) atom1746)) (SparsePolynomial.merge (SparsePolynomial.scale (50275790208000 : Int) atom1747) (SparsePolynomial.merge (SparsePolynomial.scale (106247956953600 : Int) atom1748) (SparsePolynomial.scale (48710108160000 : Int) atom1749)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14339418508800 : Int) atom1750) (SparsePolynomial.scale (45044183116800 : Int) atom1751)) (SparsePolynomial.merge (SparsePolynomial.scale (46035781747200 : Int) atom1752) (SparsePolynomial.scale (32047500441600 : Int) atom1753))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47387976652800 : Int) atom1754) (SparsePolynomial.scale (99786135859200 : Int) atom1755)) (SparsePolynomial.merge (SparsePolynomial.scale (72767900620800 : Int) atom1756) (SparsePolynomial.merge (SparsePolynomial.scale (53233189632000 : Int) atom1757) (SparsePolynomial.scale (82475129318400 : Int) atom1758))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21552701184000 : Int) atom1759) (SparsePolynomial.scale (16199976844800 : Int) atom1760)) (SparsePolynomial.merge (SparsePolynomial.scale (52191334540800 : Int) atom1761) (SparsePolynomial.merge (SparsePolynomial.scale (38734200691200 : Int) atom1762) (SparsePolynomial.scale (56190589056000 : Int) atom1763)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88662061555200 : Int) atom1764) (SparsePolynomial.scale (24355054080000 : Int) atom1765)) (SparsePolynomial.merge (SparsePolynomial.scale (19715996160000 : Int) atom1766) (SparsePolynomial.merge (SparsePolynomial.scale (48458825856000 : Int) atom1767) (SparsePolynomial.scale (29226064896000 : Int) atom1768)))))))) := by decide +kernel
theorem block023_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block023 := by
  rw [block023_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1696_nonneg g hg hA hB) (atom1697_nonneg g hg hA hB)) (add_nonneg (atom1698_nonneg g hg hA hB) (atom1699_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1700_nonneg g hg hA hB) (atom1701_nonneg g hg hA hB)) (add_nonneg (atom1702_nonneg g hg hA hB) (add_nonneg (atom1703_nonneg g hg hA hB) (atom1704_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1705_nonneg g hg hA hB) (atom1706_nonneg g hg hA hB)) (add_nonneg (atom1707_nonneg g hg hA hB) (atom1708_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1709_nonneg g hg hA hB) (atom1710_nonneg g hg hA hB)) (add_nonneg (atom1711_nonneg g hg hA hB) (add_nonneg (atom1712_nonneg g hg hA hB) (atom1713_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1714_nonneg g hg hA hB) (atom1715_nonneg g hg hA hB)) (add_nonneg (atom1716_nonneg g hg hA hB) (atom1717_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1718_nonneg g hg hA hB) (atom1719_nonneg g hg hA hB)) (add_nonneg (atom1720_nonneg g hg hA hB) (add_nonneg (atom1721_nonneg g hg hA hB) (atom1722_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1723_nonneg g hg hA hB) (atom1724_nonneg g hg hA hB)) (add_nonneg (atom1725_nonneg g hg hA hB) (atom1726_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1727_nonneg g hg hA hB) (atom1728_nonneg g hg hA hB)) (add_nonneg (atom1729_nonneg g hg hA hB) (add_nonneg (atom1730_nonneg g hg hA hB) (atom1731_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1732_nonneg g hg hA hB) (atom1733_nonneg g hg hA hB)) (add_nonneg (atom1734_nonneg g hg hA hB) (atom1735_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1736_nonneg g hg hA hB) (atom1737_nonneg g hg hA hB)) (add_nonneg (atom1738_nonneg g hg hA hB) (add_nonneg (atom1739_nonneg g hg hA hB) (atom1740_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1741_nonneg g hg hA hB) (atom1742_nonneg g hg hA hB)) (add_nonneg (atom1743_nonneg g hg hA hB) (atom1744_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1745_nonneg g hg hA hB) (atom1746_nonneg g hg hA hB)) (add_nonneg (atom1747_nonneg g hg hA hB) (add_nonneg (atom1748_nonneg g hg hA hB) (atom1749_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1750_nonneg g hg hA hB) (atom1751_nonneg g hg hA hB)) (add_nonneg (atom1752_nonneg g hg hA hB) (atom1753_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1754_nonneg g hg hA hB) (atom1755_nonneg g hg hA hB)) (add_nonneg (atom1756_nonneg g hg hA hB) (add_nonneg (atom1757_nonneg g hg hA hB) (atom1758_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1759_nonneg g hg hA hB) (atom1760_nonneg g hg hA hB)) (add_nonneg (atom1761_nonneg g hg hA hB) (add_nonneg (atom1762_nonneg g hg hA hB) (atom1763_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1764_nonneg g hg hA hB) (atom1765_nonneg g hg hA hB)) (add_nonneg (atom1766_nonneg g hg hA hB) (add_nonneg (atom1767_nonneg g hg hA hB) (atom1768_nonneg g hg hA hB))))))))

end APPT.Finite21
