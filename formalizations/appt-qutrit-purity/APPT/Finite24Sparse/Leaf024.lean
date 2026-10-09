import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1729 : SparsePolynomial.Poly := [([6,14,17], 1)]
theorem eval_atom1729 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1729 = ((g 6) * (g 14) * (g 17)) := by
  norm_num [atom1729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1729_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233230247712000 : Int) atom1729) := by
  rw [SparsePolynomial.eval_scale, eval_atom1729]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1730 : SparsePolynomial.Poly := [([6,14,18], 1)]
theorem eval_atom1730 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1730 = ((g 6) * (g 14) * (g 18)) := by
  norm_num [atom1730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1730_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257933553292800 : Int) atom1730) := by
  rw [SparsePolynomial.eval_scale, eval_atom1730]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1731 : SparsePolynomial.Poly := [([6,14,19], 1)]
theorem eval_atom1731 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1731 = ((g 6) * (g 14) * (g 19)) := by
  norm_num [atom1731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1731_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265146362157600 : Int) atom1731) := by
  rw [SparsePolynomial.eval_scale, eval_atom1731]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1732 : SparsePolynomial.Poly := [([6,14,20], 1)]
theorem eval_atom1732 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1732 = ((g 6) * (g 14) * (g 20)) := by
  norm_num [atom1732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1732_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (374918996390400 : Int) atom1732) := by
  rw [SparsePolynomial.eval_scale, eval_atom1732]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1733 : SparsePolynomial.Poly := [([6,14,21], 1)]
theorem eval_atom1733 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1733 = ((g 6) * (g 14) * (g 21)) := by
  norm_num [atom1733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1733_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (387123584601600 : Int) atom1733) := by
  rw [SparsePolynomial.eval_scale, eval_atom1733]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1734 : SparsePolynomial.Poly := [([6,14,22], 1)]
theorem eval_atom1734 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1734 = ((g 6) * (g 14) * (g 22)) := by
  norm_num [atom1734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1734_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456327657324000 : Int) atom1734) := by
  rw [SparsePolynomial.eval_scale, eval_atom1734]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1735 : SparsePolynomial.Poly := [([6,14,23], 1)]
theorem eval_atom1735 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1735 = ((g 6) * (g 14) * (g 23)) := by
  norm_num [atom1735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1735_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (541885577032800 : Int) atom1735) := by
  rw [SparsePolynomial.eval_scale, eval_atom1735]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1736 : SparsePolynomial.Poly := [([6,15,15], 1)]
theorem eval_atom1736 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1736 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom1736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1736_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152479390694400 : Int) atom1736) := by
  rw [SparsePolynomial.eval_scale, eval_atom1736]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1737 : SparsePolynomial.Poly := [([6,15,16], 1)]
theorem eval_atom1737 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1737 = ((g 6) * (g 15) * (g 16)) := by
  norm_num [atom1737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1737_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282612052800000 : Int) atom1737) := by
  rw [SparsePolynomial.eval_scale, eval_atom1737]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1738 : SparsePolynomial.Poly := [([6,15,17], 1)]
theorem eval_atom1738 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1738 = ((g 6) * (g 15) * (g 17)) := by
  norm_num [atom1738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1738_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273618079257600 : Int) atom1738) := by
  rw [SparsePolynomial.eval_scale, eval_atom1738]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1739 : SparsePolynomial.Poly := [([6,15,18], 1)]
theorem eval_atom1739 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1739 = ((g 6) * (g 15) * (g 18)) := by
  norm_num [atom1739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1739_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296810791603200 : Int) atom1739) := by
  rw [SparsePolynomial.eval_scale, eval_atom1739]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1740 : SparsePolynomial.Poly := [([6,15,19], 1)]
theorem eval_atom1740 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1740 = ((g 6) * (g 15) * (g 19)) := by
  norm_num [atom1740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1740_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (293178151526400 : Int) atom1740) := by
  rw [SparsePolynomial.eval_scale, eval_atom1740]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1741 : SparsePolynomial.Poly := [([6,15,20], 1)]
theorem eval_atom1741 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1741 = ((g 6) * (g 15) * (g 20)) := by
  norm_num [atom1741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1741_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (430387309900800 : Int) atom1741) := by
  rw [SparsePolynomial.eval_scale, eval_atom1741]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1742 : SparsePolynomial.Poly := [([6,15,21], 1)]
theorem eval_atom1742 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1742 = ((g 6) * (g 15) * (g 21)) := by
  norm_num [atom1742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1742_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450311741510400 : Int) atom1742) := by
  rw [SparsePolynomial.eval_scale, eval_atom1742]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1743 : SparsePolynomial.Poly := [([6,15,22], 1)]
theorem eval_atom1743 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1743 = ((g 6) * (g 15) * (g 22)) := by
  norm_num [atom1743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1743_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456432398553600 : Int) atom1743) := by
  rw [SparsePolynomial.eval_scale, eval_atom1743]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1744 : SparsePolynomial.Poly := [([6,15,23], 1)]
theorem eval_atom1744 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1744 = ((g 6) * (g 15) * (g 23)) := by
  norm_num [atom1744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1744_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (536413784054400 : Int) atom1744) := by
  rw [SparsePolynomial.eval_scale, eval_atom1744]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1745 : SparsePolynomial.Poly := [([6,16,16], 1)]
theorem eval_atom1745 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1745 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom1745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1745_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171232782336000 : Int) atom1745) := by
  rw [SparsePolynomial.eval_scale, eval_atom1745]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1746 : SparsePolynomial.Poly := [([6,16,17], 1)]
theorem eval_atom1746 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1746 = ((g 6) * (g 16) * (g 17)) := by
  norm_num [atom1746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1746_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324286256448000 : Int) atom1746) := by
  rw [SparsePolynomial.eval_scale, eval_atom1746]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1747 : SparsePolynomial.Poly := [([6,16,18], 1)]
theorem eval_atom1747 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1747 = ((g 6) * (g 16) * (g 18)) := by
  norm_num [atom1747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1747_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317954264544000 : Int) atom1747) := by
  rw [SparsePolynomial.eval_scale, eval_atom1747]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1748 : SparsePolynomial.Poly := [([6,16,19], 1)]
theorem eval_atom1748 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1748 = ((g 6) * (g 16) * (g 19)) := by
  norm_num [atom1748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1748_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316705906944000 : Int) atom1748) := by
  rw [SparsePolynomial.eval_scale, eval_atom1748]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1749 : SparsePolynomial.Poly := [([6,16,20], 1)]
theorem eval_atom1749 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1749 = ((g 6) * (g 16) * (g 20)) := by
  norm_num [atom1749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1749_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456299347795200 : Int) atom1749) := by
  rw [SparsePolynomial.eval_scale, eval_atom1749]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1750 : SparsePolynomial.Poly := [([6,16,21], 1)]
theorem eval_atom1750 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1750 = ((g 6) * (g 16) * (g 21)) := by
  norm_num [atom1750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1750_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (480987995241600 : Int) atom1750) := by
  rw [SparsePolynomial.eval_scale, eval_atom1750]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1751 : SparsePolynomial.Poly := [([6,16,22], 1)]
theorem eval_atom1751 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1751 = ((g 6) * (g 16) * (g 22)) := by
  norm_num [atom1751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1751_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434079871142400 : Int) atom1751) := by
  rw [SparsePolynomial.eval_scale, eval_atom1751]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1752 : SparsePolynomial.Poly := [([6,16,23], 1)]
theorem eval_atom1752 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1752 = ((g 6) * (g 16) * (g 23)) := by
  norm_num [atom1752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1752_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (596550230136000 : Int) atom1752) := by
  rw [SparsePolynomial.eval_scale, eval_atom1752]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1753 : SparsePolynomial.Poly := [([6,17,17], 1)]
theorem eval_atom1753 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1753 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom1753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1753_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189362478412800 : Int) atom1753) := by
  rw [SparsePolynomial.eval_scale, eval_atom1753]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1754 : SparsePolynomial.Poly := [([6,17,18], 1)]
theorem eval_atom1754 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1754 = ((g 6) * (g 17) * (g 18)) := by
  norm_num [atom1754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1754_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353996845171200 : Int) atom1754) := by
  rw [SparsePolynomial.eval_scale, eval_atom1754]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1755 : SparsePolynomial.Poly := [([6,17,19], 1)]
theorem eval_atom1755 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1755 = ((g 6) * (g 17) * (g 19)) := by
  norm_num [atom1755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1755_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360099139276800 : Int) atom1755) := by
  rw [SparsePolynomial.eval_scale, eval_atom1755]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1756 : SparsePolynomial.Poly := [([6,17,20], 1)]
theorem eval_atom1756 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1756 = ((g 6) * (g 17) * (g 20)) := by
  norm_num [atom1756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1756_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (507043231833600 : Int) atom1756) := by
  rw [SparsePolynomial.eval_scale, eval_atom1756]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1757 : SparsePolynomial.Poly := [([6,17,21], 1)]
theorem eval_atom1757 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1757 = ((g 6) * (g 17) * (g 21)) := by
  norm_num [atom1757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1757_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (538979279731200 : Int) atom1757) := by
  rw [SparsePolynomial.eval_scale, eval_atom1757]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1758 : SparsePolynomial.Poly := [([6,17,22], 1)]
theorem eval_atom1758 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1758 = ((g 6) * (g 17) * (g 22)) := by
  norm_num [atom1758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1758_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (498194873164800 : Int) atom1758) := by
  rw [SparsePolynomial.eval_scale, eval_atom1758]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1759 : SparsePolynomial.Poly := [([6,17,23], 1)]
theorem eval_atom1759 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1759 = ((g 6) * (g 17) * (g 23)) := by
  norm_num [atom1759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1759_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (667861006982400 : Int) atom1759) := by
  rw [SparsePolynomial.eval_scale, eval_atom1759]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1760 : SparsePolynomial.Poly := [([6,18,18], 1)]
theorem eval_atom1760 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1760 = ((g 6) * (g 18) * (g 18)) := by
  norm_num [atom1760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1760_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215504536262400 : Int) atom1760) := by
  rw [SparsePolynomial.eval_scale, eval_atom1760]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1761 : SparsePolynomial.Poly := [([6,18,19], 1)]
theorem eval_atom1761 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1761 = ((g 6) * (g 18) * (g 19)) := by
  norm_num [atom1761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1761_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411554023372800 : Int) atom1761) := by
  rw [SparsePolynomial.eval_scale, eval_atom1761]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1762 : SparsePolynomial.Poly := [([6,18,20], 1)]
theorem eval_atom1762 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1762 = ((g 6) * (g 18) * (g 20)) := by
  norm_num [atom1762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1762_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (603361671897600 : Int) atom1762) := by
  rw [SparsePolynomial.eval_scale, eval_atom1762]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1763 : SparsePolynomial.Poly := [([6,18,21], 1)]
theorem eval_atom1763 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1763 = ((g 6) * (g 18) * (g 21)) := by
  norm_num [atom1763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1763_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (596010214800000 : Int) atom1763) := by
  rw [SparsePolynomial.eval_scale, eval_atom1763]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1764 : SparsePolynomial.Poly := [([6,18,22], 1)]
theorem eval_atom1764 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1764 = ((g 6) * (g 18) * (g 22)) := by
  norm_num [atom1764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1764_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (459421369344000 : Int) atom1764) := by
  rw [SparsePolynomial.eval_scale, eval_atom1764]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1765 : SparsePolynomial.Poly := [([6,18,23], 1)]
theorem eval_atom1765 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1765 = ((g 6) * (g 18) * (g 23)) := by
  norm_num [atom1765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1765_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (653633837841600 : Int) atom1765) := by
  rw [SparsePolynomial.eval_scale, eval_atom1765]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1766 : SparsePolynomial.Poly := [([6,19,19], 1)]
theorem eval_atom1766 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1766 = ((g 6) * (g 19) * (g 19)) := by
  norm_num [atom1766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1766_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140688709539840 : Int) atom1766) := by
  rw [SparsePolynomial.eval_scale, eval_atom1766]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1767 : SparsePolynomial.Poly := [([6,19,20], 1)]
theorem eval_atom1767 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1767 = ((g 6) * (g 19) * (g 20)) := by
  norm_num [atom1767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1767_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444000367641600 : Int) atom1767) := by
  rw [SparsePolynomial.eval_scale, eval_atom1767]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1768 : SparsePolynomial.Poly := [([6,19,21], 1)]
theorem eval_atom1768 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1768 = ((g 6) * (g 19) * (g 21)) := by
  norm_num [atom1768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1768_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440555867136000 : Int) atom1768) := by
  rw [SparsePolynomial.eval_scale, eval_atom1768]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1769 : SparsePolynomial.Poly := [([6,19,22], 1)]
theorem eval_atom1769 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1769 = ((g 6) * (g 19) * (g 22)) := by
  norm_num [atom1769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1769_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373855556793600 : Int) atom1769) := by
  rw [SparsePolynomial.eval_scale, eval_atom1769]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1770 : SparsePolynomial.Poly := [([6,19,23], 1)]
theorem eval_atom1770 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1770 = ((g 6) * (g 19) * (g 23)) := by
  norm_num [atom1770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1770_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427044288787200 : Int) atom1770) := by
  rw [SparsePolynomial.eval_scale, eval_atom1770]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1771 : SparsePolynomial.Poly := [([6,20,20], 1)]
theorem eval_atom1771 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1771 = ((g 6) * (g 20) * (g 20)) := by
  norm_num [atom1771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1771_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318371779756800 : Int) atom1771) := by
  rw [SparsePolynomial.eval_scale, eval_atom1771]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1772 : SparsePolynomial.Poly := [([6,20,21], 1)]
theorem eval_atom1772 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1772 = ((g 6) * (g 20) * (g 21)) := by
  norm_num [atom1772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1772_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461153767536000 : Int) atom1772) := by
  rw [SparsePolynomial.eval_scale, eval_atom1772]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1773 : SparsePolynomial.Poly := [([6,20,22], 1)]
theorem eval_atom1773 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1773 = ((g 6) * (g 20) * (g 22)) := by
  norm_num [atom1773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1773_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (366896969913600 : Int) atom1773) := by
  rw [SparsePolynomial.eval_scale, eval_atom1773]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1774 : SparsePolynomial.Poly := [([6,20,23], 1)]
theorem eval_atom1774 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1774 = ((g 6) * (g 20) * (g 23)) := by
  norm_num [atom1774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1774_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (448745173531200 : Int) atom1774) := by
  rw [SparsePolynomial.eval_scale, eval_atom1774]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1775 : SparsePolynomial.Poly := [([6,21,21], 1)]
theorem eval_atom1775 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1775 = ((g 6) * (g 21) * (g 21)) := by
  norm_num [atom1775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1775_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95265953798400 : Int) atom1775) := by
  rw [SparsePolynomial.eval_scale, eval_atom1775]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1776 : SparsePolynomial.Poly := [([6,21,22], 1)]
theorem eval_atom1776 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1776 = ((g 6) * (g 21) * (g 22)) := by
  norm_num [atom1776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1776_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154961447760000 : Int) atom1776) := by
  rw [SparsePolynomial.eval_scale, eval_atom1776]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1777 : SparsePolynomial.Poly := [([6,21,23], 1)]
theorem eval_atom1777 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1777 = ((g 6) * (g 21) * (g 23)) := by
  norm_num [atom1777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1777_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232770529958400 : Int) atom1777) := by
  rw [SparsePolynomial.eval_scale, eval_atom1777]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1778 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom1778 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1778 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom1778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1778_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12511711027200 : Int) atom1778) := by
  rw [SparsePolynomial.eval_scale, eval_atom1778]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1779 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom1779 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1779 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom1779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1779_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21812807385600 : Int) atom1779) := by
  rw [SparsePolynomial.eval_scale, eval_atom1779]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1780 : SparsePolynomial.Poly := [([7,7,9], 1)]
theorem eval_atom1780 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1780 = ((g 7) * (g 7) * (g 9)) := by
  norm_num [atom1780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1780_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1780) := by
  rw [SparsePolynomial.eval_scale, eval_atom1780]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1781 : SparsePolynomial.Poly := [([7,7,10], 1)]
theorem eval_atom1781 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1781 = ((g 7) * (g 7) * (g 10)) := by
  norm_num [atom1781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1781_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3663191356704 : Int) atom1781) := by
  rw [SparsePolynomial.eval_scale, eval_atom1781]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1782 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom1782 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1782 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom1782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1782_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28692358464000 : Int) atom1782) := by
  rw [SparsePolynomial.eval_scale, eval_atom1782]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1783 : SparsePolynomial.Poly := [([7,8,9], 1)]
theorem eval_atom1783 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1783 = ((g 7) * (g 8) * (g 9)) := by
  norm_num [atom1783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1783_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24022245970800 : Int) atom1783) := by
  rw [SparsePolynomial.eval_scale, eval_atom1783]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1784 : SparsePolynomial.Poly := [([7,8,13], 1)]
theorem eval_atom1784 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1784 = ((g 7) * (g 8) * (g 13)) := by
  norm_num [atom1784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1784_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1784) := by
  rw [SparsePolynomial.eval_scale, eval_atom1784]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1785 : SparsePolynomial.Poly := [([7,8,14], 1)]
theorem eval_atom1785 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1785 = ((g 7) * (g 8) * (g 14)) := by
  norm_num [atom1785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1785_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom1785) := by
  rw [SparsePolynomial.eval_scale, eval_atom1785]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1786 : SparsePolynomial.Poly := [([7,8,15], 1)]
theorem eval_atom1786 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1786 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom1786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1786_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom1786) := by
  rw [SparsePolynomial.eval_scale, eval_atom1786]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1787 : SparsePolynomial.Poly := [([7,8,16], 1)]
theorem eval_atom1787 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1787 = ((g 7) * (g 8) * (g 16)) := by
  norm_num [atom1787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1787_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom1787) := by
  rw [SparsePolynomial.eval_scale, eval_atom1787]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1788 : SparsePolynomial.Poly := [([7,8,17], 1)]
theorem eval_atom1788 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1788 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom1788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1788_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15415202880000 : Int) atom1788) := by
  rw [SparsePolynomial.eval_scale, eval_atom1788]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1789 : SparsePolynomial.Poly := [([7,8,18], 1)]
theorem eval_atom1789 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1789 = ((g 7) * (g 8) * (g 18)) := by
  norm_num [atom1789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1789_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (822852898560 : Int) atom1789) := by
  rw [SparsePolynomial.eval_scale, eval_atom1789]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1790 : SparsePolynomial.Poly := [([7,8,21], 1)]
theorem eval_atom1790 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1790 = ((g 7) * (g 8) * (g 21)) := by
  norm_num [atom1790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1790_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41615732188800 : Int) atom1790) := by
  rw [SparsePolynomial.eval_scale, eval_atom1790]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1791 : SparsePolynomial.Poly := [([7,8,22], 1)]
theorem eval_atom1791 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1791 = ((g 7) * (g 8) * (g 22)) := by
  norm_num [atom1791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1791_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84054317276160 : Int) atom1791) := by
  rw [SparsePolynomial.eval_scale, eval_atom1791]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1792 : SparsePolynomial.Poly := [([7,8,23], 1)]
theorem eval_atom1792 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1792 = ((g 7) * (g 8) * (g 23)) := by
  norm_num [atom1792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1792_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134354124273600 : Int) atom1792) := by
  rw [SparsePolynomial.eval_scale, eval_atom1792]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1793 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom1793 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1793 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom1793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1793_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21014804857200 : Int) atom1793) := by
  rw [SparsePolynomial.eval_scale, eval_atom1793]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1794 : SparsePolynomial.Poly := [([7,9,10], 1)]
theorem eval_atom1794 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1794 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom1794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1794_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20007883720704 : Int) atom1794) := by
  rw [SparsePolynomial.eval_scale, eval_atom1794]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1795 : SparsePolynomial.Poly := [([7,9,11], 1)]
theorem eval_atom1795 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1795 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom1795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1795_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27833005200 : Int) atom1795) := by
  rw [SparsePolynomial.eval_scale, eval_atom1795]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1796 : SparsePolynomial.Poly := [([7,9,12], 1)]
theorem eval_atom1796 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1796 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom1796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1796_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5173321414800 : Int) atom1796) := by
  rw [SparsePolynomial.eval_scale, eval_atom1796]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1797 : SparsePolynomial.Poly := [([7,9,13], 1)]
theorem eval_atom1797 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1797 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom1797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1797_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7235769248400 : Int) atom1797) := by
  rw [SparsePolynomial.eval_scale, eval_atom1797]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1798 : SparsePolynomial.Poly := [([7,9,14], 1)]
theorem eval_atom1798 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1798 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom1798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1798_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12381257658000 : Int) atom1798) := by
  rw [SparsePolynomial.eval_scale, eval_atom1798]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1799 : SparsePolynomial.Poly := [([7,9,15], 1)]
theorem eval_atom1799 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1799 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom1799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1799_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17526746067600 : Int) atom1799) := by
  rw [SparsePolynomial.eval_scale, eval_atom1799]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1800 : SparsePolynomial.Poly := [([7,9,16], 1)]
theorem eval_atom1800 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1800 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom1800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1800_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22672234477200 : Int) atom1800) := by
  rw [SparsePolynomial.eval_scale, eval_atom1800]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1801 : SparsePolynomial.Poly := [([7,9,17], 1)]
theorem eval_atom1801 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1801 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom1801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1801_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27817722886800 : Int) atom1801) := by
  rw [SparsePolynomial.eval_scale, eval_atom1801]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1802 : SparsePolynomial.Poly := [([7,9,18], 1)]
theorem eval_atom1802 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1802 = ((g 7) * (g 9) * (g 18)) := by
  norm_num [atom1802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1802_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (743215066440 : Int) atom1802) := by
  rw [SparsePolynomial.eval_scale, eval_atom1802]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1803 : SparsePolynomial.Poly := [([7,9,21], 1)]
theorem eval_atom1803 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1803 = ((g 7) * (g 9) * (g 21)) := by
  norm_num [atom1803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1803_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80451799866900 : Int) atom1803) := by
  rw [SparsePolynomial.eval_scale, eval_atom1803]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1804 : SparsePolynomial.Poly := [([7,9,22], 1)]
theorem eval_atom1804 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1804 = ((g 7) * (g 9) * (g 22)) := by
  norm_num [atom1804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1804_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161646814800240 : Int) atom1804) := by
  rw [SparsePolynomial.eval_scale, eval_atom1804]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1805 : SparsePolynomial.Poly := [([7,9,23], 1)]
theorem eval_atom1805 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1805 = ((g 7) * (g 9) * (g 23)) := by
  norm_num [atom1805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1805_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257479651979550 : Int) atom1805) := by
  rw [SparsePolynomial.eval_scale, eval_atom1805]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1806 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom1806 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1806 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom1806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1806_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24677996213904 : Int) atom1806) := by
  rw [SparsePolynomial.eval_scale, eval_atom1806]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1807 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom1807 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1807 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom1807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1807_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37625733046704 : Int) atom1807) := by
  rw [SparsePolynomial.eval_scale, eval_atom1807]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1808 : SparsePolynomial.Poly := [([7,10,12], 1)]
theorem eval_atom1808 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1808 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom1808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1808_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40730035971504 : Int) atom1808) := by
  rw [SparsePolynomial.eval_scale, eval_atom1808]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block024 : SparsePolynomial.Poly := [([6,14,17], 233230247712000), ([6,14,18], 257933553292800), ([6,14,19], 265146362157600), ([6,14,20], 374918996390400), ([6,14,21], 387123584601600), ([6,14,22], 456327657324000), ([6,14,23], 541885577032800), ([6,15,15], 152479390694400), ([6,15,16], 282612052800000), ([6,15,17], 273618079257600), ([6,15,18], 296810791603200), ([6,15,19], 293178151526400), ([6,15,20], 430387309900800), ([6,15,21], 450311741510400), ([6,15,22], 456432398553600), ([6,15,23], 536413784054400), ([6,16,16], 171232782336000), ([6,16,17], 324286256448000), ([6,16,18], 317954264544000), ([6,16,19], 316705906944000), ([6,16,20], 456299347795200), ([6,16,21], 480987995241600), ([6,16,22], 434079871142400), ([6,16,23], 596550230136000), ([6,17,17], 189362478412800), ([6,17,18], 353996845171200), ([6,17,19], 360099139276800), ([6,17,20], 507043231833600), ([6,17,21], 538979279731200), ([6,17,22], 498194873164800), ([6,17,23], 667861006982400), ([6,18,18], 215504536262400), ([6,18,19], 411554023372800), ([6,18,20], 603361671897600), ([6,18,21], 596010214800000), ([6,18,22], 459421369344000), ([6,18,23], 653633837841600), ([6,19,19], 140688709539840), ([6,19,20], 444000367641600), ([6,19,21], 440555867136000), ([6,19,22], 373855556793600), ([6,19,23], 427044288787200), ([6,20,20], 318371779756800), ([6,20,21], 461153767536000), ([6,20,22], 366896969913600), ([6,20,23], 448745173531200), ([6,21,21], 95265953798400), ([6,21,22], 154961447760000), ([6,21,23], 232770529958400), ([7,7,7], 12511711027200), ([7,7,8], 21812807385600), ([7,7,9], 3083040576000), ([7,7,10], 3663191356704), ([7,8,8], 28692358464000), ([7,8,9], 24022245970800), ([7,8,13], 3083040576000), ([7,8,14], 6166081152000), ([7,8,15], 9249121728000), ([7,8,16], 12332162304000), ([7,8,17], 15415202880000), ([7,8,18], 822852898560), ([7,8,21], 41615732188800), ([7,8,22], 84054317276160), ([7,8,23], 134354124273600), ([7,9,9], 21014804857200), ([7,9,10], 20007883720704), ([7,9,11], 27833005200), ([7,9,12], 5173321414800), ([7,9,13], 7235769248400), ([7,9,14], 12381257658000), ([7,9,15], 17526746067600), ([7,9,16], 22672234477200), ([7,9,17], 27817722886800), ([7,9,18], 743215066440), ([7,9,21], 80451799866900), ([7,9,22], 161646814800240), ([7,9,23], 257479651979550), ([7,10,10], 24677996213904), ([7,10,11], 37625733046704), ([7,10,12], 40730035971504)]
theorem block024_data : block024 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (233230247712000 : Int) atom1729) (SparsePolynomial.scale (257933553292800 : Int) atom1730)) (SparsePolynomial.merge (SparsePolynomial.scale (265146362157600 : Int) atom1731) (SparsePolynomial.merge (SparsePolynomial.scale (374918996390400 : Int) atom1732) (SparsePolynomial.scale (387123584601600 : Int) atom1733)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (456327657324000 : Int) atom1734) (SparsePolynomial.scale (541885577032800 : Int) atom1735)) (SparsePolynomial.merge (SparsePolynomial.scale (152479390694400 : Int) atom1736) (SparsePolynomial.merge (SparsePolynomial.scale (282612052800000 : Int) atom1737) (SparsePolynomial.scale (273618079257600 : Int) atom1738))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (296810791603200 : Int) atom1739) (SparsePolynomial.scale (293178151526400 : Int) atom1740)) (SparsePolynomial.merge (SparsePolynomial.scale (430387309900800 : Int) atom1741) (SparsePolynomial.merge (SparsePolynomial.scale (450311741510400 : Int) atom1742) (SparsePolynomial.scale (456432398553600 : Int) atom1743)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (536413784054400 : Int) atom1744) (SparsePolynomial.scale (171232782336000 : Int) atom1745)) (SparsePolynomial.merge (SparsePolynomial.scale (324286256448000 : Int) atom1746) (SparsePolynomial.merge (SparsePolynomial.scale (317954264544000 : Int) atom1747) (SparsePolynomial.scale (316705906944000 : Int) atom1748)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (456299347795200 : Int) atom1749) (SparsePolynomial.scale (480987995241600 : Int) atom1750)) (SparsePolynomial.merge (SparsePolynomial.scale (434079871142400 : Int) atom1751) (SparsePolynomial.merge (SparsePolynomial.scale (596550230136000 : Int) atom1752) (SparsePolynomial.scale (189362478412800 : Int) atom1753)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (353996845171200 : Int) atom1754) (SparsePolynomial.scale (360099139276800 : Int) atom1755)) (SparsePolynomial.merge (SparsePolynomial.scale (507043231833600 : Int) atom1756) (SparsePolynomial.merge (SparsePolynomial.scale (538979279731200 : Int) atom1757) (SparsePolynomial.scale (498194873164800 : Int) atom1758))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (667861006982400 : Int) atom1759) (SparsePolynomial.scale (215504536262400 : Int) atom1760)) (SparsePolynomial.merge (SparsePolynomial.scale (411554023372800 : Int) atom1761) (SparsePolynomial.merge (SparsePolynomial.scale (603361671897600 : Int) atom1762) (SparsePolynomial.scale (596010214800000 : Int) atom1763)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (459421369344000 : Int) atom1764) (SparsePolynomial.scale (653633837841600 : Int) atom1765)) (SparsePolynomial.merge (SparsePolynomial.scale (140688709539840 : Int) atom1766) (SparsePolynomial.merge (SparsePolynomial.scale (444000367641600 : Int) atom1767) (SparsePolynomial.scale (440555867136000 : Int) atom1768))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (373855556793600 : Int) atom1769) (SparsePolynomial.scale (427044288787200 : Int) atom1770)) (SparsePolynomial.merge (SparsePolynomial.scale (318371779756800 : Int) atom1771) (SparsePolynomial.merge (SparsePolynomial.scale (461153767536000 : Int) atom1772) (SparsePolynomial.scale (366896969913600 : Int) atom1773)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (448745173531200 : Int) atom1774) (SparsePolynomial.scale (95265953798400 : Int) atom1775)) (SparsePolynomial.merge (SparsePolynomial.scale (154961447760000 : Int) atom1776) (SparsePolynomial.merge (SparsePolynomial.scale (232770529958400 : Int) atom1777) (SparsePolynomial.scale (12511711027200 : Int) atom1778))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21812807385600 : Int) atom1779) (SparsePolynomial.scale (3083040576000 : Int) atom1780)) (SparsePolynomial.merge (SparsePolynomial.scale (3663191356704 : Int) atom1781) (SparsePolynomial.merge (SparsePolynomial.scale (28692358464000 : Int) atom1782) (SparsePolynomial.scale (24022245970800 : Int) atom1783)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom1784) (SparsePolynomial.scale (6166081152000 : Int) atom1785)) (SparsePolynomial.merge (SparsePolynomial.scale (9249121728000 : Int) atom1786) (SparsePolynomial.merge (SparsePolynomial.scale (12332162304000 : Int) atom1787) (SparsePolynomial.scale (15415202880000 : Int) atom1788)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (822852898560 : Int) atom1789) (SparsePolynomial.scale (41615732188800 : Int) atom1790)) (SparsePolynomial.merge (SparsePolynomial.scale (84054317276160 : Int) atom1791) (SparsePolynomial.merge (SparsePolynomial.scale (134354124273600 : Int) atom1792) (SparsePolynomial.scale (21014804857200 : Int) atom1793)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20007883720704 : Int) atom1794) (SparsePolynomial.scale (27833005200 : Int) atom1795)) (SparsePolynomial.merge (SparsePolynomial.scale (5173321414800 : Int) atom1796) (SparsePolynomial.merge (SparsePolynomial.scale (7235769248400 : Int) atom1797) (SparsePolynomial.scale (12381257658000 : Int) atom1798))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17526746067600 : Int) atom1799) (SparsePolynomial.scale (22672234477200 : Int) atom1800)) (SparsePolynomial.merge (SparsePolynomial.scale (27817722886800 : Int) atom1801) (SparsePolynomial.merge (SparsePolynomial.scale (743215066440 : Int) atom1802) (SparsePolynomial.scale (80451799866900 : Int) atom1803)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (161646814800240 : Int) atom1804) (SparsePolynomial.scale (257479651979550 : Int) atom1805)) (SparsePolynomial.merge (SparsePolynomial.scale (24677996213904 : Int) atom1806) (SparsePolynomial.merge (SparsePolynomial.scale (37625733046704 : Int) atom1807) (SparsePolynomial.scale (40730035971504 : Int) atom1808)))))))) := by decide +kernel
theorem block024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block024 := by
  rw [block024_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1729_nonneg g hg hA hB) (atom1730_nonneg g hg hA hB)) (add_nonneg (atom1731_nonneg g hg hA hB) (add_nonneg (atom1732_nonneg g hg hA hB) (atom1733_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1734_nonneg g hg hA hB) (atom1735_nonneg g hg hA hB)) (add_nonneg (atom1736_nonneg g hg hA hB) (add_nonneg (atom1737_nonneg g hg hA hB) (atom1738_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1739_nonneg g hg hA hB) (atom1740_nonneg g hg hA hB)) (add_nonneg (atom1741_nonneg g hg hA hB) (add_nonneg (atom1742_nonneg g hg hA hB) (atom1743_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1744_nonneg g hg hA hB) (atom1745_nonneg g hg hA hB)) (add_nonneg (atom1746_nonneg g hg hA hB) (add_nonneg (atom1747_nonneg g hg hA hB) (atom1748_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1749_nonneg g hg hA hB) (atom1750_nonneg g hg hA hB)) (add_nonneg (atom1751_nonneg g hg hA hB) (add_nonneg (atom1752_nonneg g hg hA hB) (atom1753_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1754_nonneg g hg hA hB) (atom1755_nonneg g hg hA hB)) (add_nonneg (atom1756_nonneg g hg hA hB) (add_nonneg (atom1757_nonneg g hg hA hB) (atom1758_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1759_nonneg g hg hA hB) (atom1760_nonneg g hg hA hB)) (add_nonneg (atom1761_nonneg g hg hA hB) (add_nonneg (atom1762_nonneg g hg hA hB) (atom1763_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1764_nonneg g hg hA hB) (atom1765_nonneg g hg hA hB)) (add_nonneg (atom1766_nonneg g hg hA hB) (add_nonneg (atom1767_nonneg g hg hA hB) (atom1768_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1769_nonneg g hg hA hB) (atom1770_nonneg g hg hA hB)) (add_nonneg (atom1771_nonneg g hg hA hB) (add_nonneg (atom1772_nonneg g hg hA hB) (atom1773_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1774_nonneg g hg hA hB) (atom1775_nonneg g hg hA hB)) (add_nonneg (atom1776_nonneg g hg hA hB) (add_nonneg (atom1777_nonneg g hg hA hB) (atom1778_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1779_nonneg g hg hA hB) (atom1780_nonneg g hg hA hB)) (add_nonneg (atom1781_nonneg g hg hA hB) (add_nonneg (atom1782_nonneg g hg hA hB) (atom1783_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1784_nonneg g hg hA hB) (atom1785_nonneg g hg hA hB)) (add_nonneg (atom1786_nonneg g hg hA hB) (add_nonneg (atom1787_nonneg g hg hA hB) (atom1788_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1789_nonneg g hg hA hB) (atom1790_nonneg g hg hA hB)) (add_nonneg (atom1791_nonneg g hg hA hB) (add_nonneg (atom1792_nonneg g hg hA hB) (atom1793_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1794_nonneg g hg hA hB) (atom1795_nonneg g hg hA hB)) (add_nonneg (atom1796_nonneg g hg hA hB) (add_nonneg (atom1797_nonneg g hg hA hB) (atom1798_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1799_nonneg g hg hA hB) (atom1800_nonneg g hg hA hB)) (add_nonneg (atom1801_nonneg g hg hA hB) (add_nonneg (atom1802_nonneg g hg hA hB) (atom1803_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1804_nonneg g hg hA hB) (atom1805_nonneg g hg hA hB)) (add_nonneg (atom1806_nonneg g hg hA hB) (add_nonneg (atom1807_nonneg g hg hA hB) (atom1808_nonneg g hg hA hB))))))))

end APPT.Finite24
