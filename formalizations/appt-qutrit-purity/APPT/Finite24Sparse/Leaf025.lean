import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1809 : SparsePolynomial.Poly := [([7,10,13], 1)]
theorem eval_atom1809 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1809 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom1809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1809_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46917379472304 : Int) atom1809) := by
  rw [SparsePolynomial.eval_scale, eval_atom1809]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1810 : SparsePolynomial.Poly := [([7,10,14], 1)]
theorem eval_atom1810 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1810 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom1810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1810_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53104722973104 : Int) atom1810) := by
  rw [SparsePolynomial.eval_scale, eval_atom1810]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1811 : SparsePolynomial.Poly := [([7,10,15], 1)]
theorem eval_atom1811 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1811 = ((g 7) * (g 10) * (g 15)) := by
  norm_num [atom1811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1811_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59292066473904 : Int) atom1811) := by
  rw [SparsePolynomial.eval_scale, eval_atom1811]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1812 : SparsePolynomial.Poly := [([7,10,16], 1)]
theorem eval_atom1812 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1812 = ((g 7) * (g 10) * (g 16)) := by
  norm_num [atom1812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1812_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65479409974704 : Int) atom1812) := by
  rw [SparsePolynomial.eval_scale, eval_atom1812]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1813 : SparsePolynomial.Poly := [([7,10,17], 1)]
theorem eval_atom1813 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1813 = ((g 7) * (g 10) * (g 17)) := by
  norm_num [atom1813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1813_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71666753475504 : Int) atom1813) := by
  rw [SparsePolynomial.eval_scale, eval_atom1813]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1814 : SparsePolynomial.Poly := [([7,10,18], 1)]
theorem eval_atom1814 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1814 = ((g 7) * (g 10) * (g 18)) := by
  norm_num [atom1814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1814_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53145950625240 : Int) atom1814) := by
  rw [SparsePolynomial.eval_scale, eval_atom1814]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1815 : SparsePolynomial.Poly := [([7,10,19], 1)]
theorem eval_atom1815 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1815 = ((g 7) * (g 10) * (g 19)) := by
  norm_num [atom1815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1815_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60258778990080 : Int) atom1815) := by
  rw [SparsePolynomial.eval_scale, eval_atom1815]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1816 : SparsePolynomial.Poly := [([7,10,20], 1)]
theorem eval_atom1816 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1816 = ((g 7) * (g 10) * (g 20)) := by
  norm_num [atom1816, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1816_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67371607354920 : Int) atom1816) := by
  rw [SparsePolynomial.eval_scale, eval_atom1816]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1817 : SparsePolynomial.Poly := [([7,10,21], 1)]
theorem eval_atom1817 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1817 = ((g 7) * (g 10) * (g 21)) := by
  norm_num [atom1817, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1817_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150922586933052 : Int) atom1817) := by
  rw [SparsePolynomial.eval_scale, eval_atom1817]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1818 : SparsePolynomial.Poly := [([7,10,22], 1)]
theorem eval_atom1818 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1818 = ((g 7) * (g 10) * (g 22)) := by
  norm_num [atom1818, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1818_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (234473566511184 : Int) atom1818) := by
  rw [SparsePolynomial.eval_scale, eval_atom1818]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1819 : SparsePolynomial.Poly := [([7,10,23], 1)]
theorem eval_atom1819 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1819 = ((g 7) * (g 10) * (g 23)) := by
  norm_num [atom1819, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1819_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330609990480858 : Int) atom1819) := by
  rw [SparsePolynomial.eval_scale, eval_atom1819]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1820 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom1820 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1820 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom1820, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1820_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44798735335200 : Int) atom1820) := by
  rw [SparsePolynomial.eval_scale, eval_atom1820]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1821 : SparsePolynomial.Poly := [([7,11,12], 1)]
theorem eval_atom1821 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1821 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom1821, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1821_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72945064869600 : Int) atom1821) := by
  rw [SparsePolynomial.eval_scale, eval_atom1821]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1822 : SparsePolynomial.Poly := [([7,11,13], 1)]
theorem eval_atom1822 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1822 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom1822, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1822_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76070630143200 : Int) atom1822) := by
  rw [SparsePolynomial.eval_scale, eval_atom1822]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1823 : SparsePolynomial.Poly := [([7,11,14], 1)]
theorem eval_atom1823 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1823 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom1823, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1823_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79196195416800 : Int) atom1823) := by
  rw [SparsePolynomial.eval_scale, eval_atom1823]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1824 : SparsePolynomial.Poly := [([7,11,15], 1)]
theorem eval_atom1824 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1824 = ((g 7) * (g 11) * (g 15)) := by
  norm_num [atom1824, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1824_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82321760690400 : Int) atom1824) := by
  rw [SparsePolynomial.eval_scale, eval_atom1824]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1825 : SparsePolynomial.Poly := [([7,11,16], 1)]
theorem eval_atom1825 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1825 = ((g 7) * (g 11) * (g 16)) := by
  norm_num [atom1825, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1825_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88530366540000 : Int) atom1825) := by
  rw [SparsePolynomial.eval_scale, eval_atom1825]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1826 : SparsePolynomial.Poly := [([7,11,17], 1)]
theorem eval_atom1826 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1826 = ((g 7) * (g 11) * (g 17)) := by
  norm_num [atom1826, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1826_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94738972389600 : Int) atom1826) := by
  rw [SparsePolynomial.eval_scale, eval_atom1826]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1827 : SparsePolynomial.Poly := [([7,11,18], 1)]
theorem eval_atom1827 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1827 = ((g 7) * (g 11) * (g 18)) := by
  norm_num [atom1827, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1827_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100163032583856 : Int) atom1827) := by
  rw [SparsePolynomial.eval_scale, eval_atom1827]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1828 : SparsePolynomial.Poly := [([7,11,19], 1)]
theorem eval_atom1828 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1828 = ((g 7) * (g 11) * (g 19)) := by
  norm_num [atom1828, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1828_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108467813667840 : Int) atom1828) := by
  rw [SparsePolynomial.eval_scale, eval_atom1828]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1829 : SparsePolynomial.Poly := [([7,11,20], 1)]
theorem eval_atom1829 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1829 = ((g 7) * (g 11) * (g 20)) := by
  norm_num [atom1829, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1829_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (138689388522960 : Int) atom1829) := by
  rw [SparsePolynomial.eval_scale, eval_atom1829]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1830 : SparsePolynomial.Poly := [([7,11,21], 1)]
theorem eval_atom1830 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1830 = ((g 7) * (g 11) * (g 21)) := by
  norm_num [atom1830, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1830_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219887061777240 : Int) atom1830) := by
  rw [SparsePolynomial.eval_scale, eval_atom1830]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1831 : SparsePolynomial.Poly := [([7,11,22], 1)]
theorem eval_atom1831 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1831 = ((g 7) * (g 11) * (g 22)) := by
  norm_num [atom1831, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1831_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311372780684064 : Int) atom1831) := by
  rw [SparsePolynomial.eval_scale, eval_atom1831]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1832 : SparsePolynomial.Poly := [([7,11,23], 1)]
theorem eval_atom1832 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1832 = ((g 7) * (g 11) * (g 23)) := by
  norm_num [atom1832, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1832_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (412496377316100 : Int) atom1832) := by
  rw [SparsePolynomial.eval_scale, eval_atom1832]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1833 : SparsePolynomial.Poly := [([7,12,12], 1)]
theorem eval_atom1833 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1833 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom1833, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1833_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59997328036800 : Int) atom1833) := by
  rw [SparsePolynomial.eval_scale, eval_atom1833]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1834 : SparsePolynomial.Poly := [([7,12,13], 1)]
theorem eval_atom1834 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1834 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom1834, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1834_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113390038977600 : Int) atom1834) := by
  rw [SparsePolynomial.eval_scale, eval_atom1834]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1835 : SparsePolynomial.Poly := [([7,12,14], 1)]
theorem eval_atom1835 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1835 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom1835, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1835_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118599314433600 : Int) atom1835) := by
  rw [SparsePolynomial.eval_scale, eval_atom1835]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1836 : SparsePolynomial.Poly := [([7,12,15], 1)]
theorem eval_atom1836 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1836 = ((g 7) * (g 12) * (g 15)) := by
  norm_num [atom1836, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1836_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123808589889600 : Int) atom1836) := by
  rw [SparsePolynomial.eval_scale, eval_atom1836]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1837 : SparsePolynomial.Poly := [([7,12,16], 1)]
theorem eval_atom1837 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1837 = ((g 7) * (g 12) * (g 16)) := by
  norm_num [atom1837, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1837_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129017865345600 : Int) atom1837) := by
  rw [SparsePolynomial.eval_scale, eval_atom1837]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1838 : SparsePolynomial.Poly := [([7,12,17], 1)]
theorem eval_atom1838 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1838 = ((g 7) * (g 12) * (g 17)) := by
  norm_num [atom1838, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1838_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134227140801600 : Int) atom1838) := by
  rw [SparsePolynomial.eval_scale, eval_atom1838]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1839 : SparsePolynomial.Poly := [([7,12,18], 1)]
theorem eval_atom1839 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1839 = ((g 7) * (g 12) * (g 18)) := by
  norm_num [atom1839, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1839_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180233184363936 : Int) atom1839) := by
  rw [SparsePolynomial.eval_scale, eval_atom1839]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1840 : SparsePolynomial.Poly := [([7,12,19], 1)]
theorem eval_atom1840 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1840 = ((g 7) * (g 12) * (g 19)) := by
  norm_num [atom1840, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1840_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168555211376640 : Int) atom1840) := by
  rw [SparsePolynomial.eval_scale, eval_atom1840]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1841 : SparsePolynomial.Poly := [([7,12,20], 1)]
theorem eval_atom1841 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1841 = ((g 7) * (g 12) * (g 20)) := by
  norm_num [atom1841, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1841_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266923278584160 : Int) atom1841) := by
  rw [SparsePolynomial.eval_scale, eval_atom1841]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1842 : SparsePolynomial.Poly := [([7,12,21], 1)]
theorem eval_atom1842 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1842 = ((g 7) * (g 12) * (g 21)) := by
  norm_num [atom1842, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1842_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283378760863440 : Int) atom1842) := by
  rw [SparsePolynomial.eval_scale, eval_atom1842]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1843 : SparsePolynomial.Poly := [([7,12,22], 1)]
theorem eval_atom1843 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1843 = ((g 7) * (g 12) * (g 22)) := by
  norm_num [atom1843, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1843_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369508560552384 : Int) atom1843) := by
  rw [SparsePolynomial.eval_scale, eval_atom1843]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1844 : SparsePolynomial.Poly := [([7,12,23], 1)]
theorem eval_atom1844 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1844 = ((g 7) * (g 12) * (g 23)) := by
  norm_num [atom1844, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1844_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461296956166200 : Int) atom1844) := by
  rw [SparsePolynomial.eval_scale, eval_atom1844]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1845 : SparsePolynomial.Poly := [([7,13,13], 1)]
theorem eval_atom1845 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1845 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom1845, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1845_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85243709443200 : Int) atom1845) := by
  rw [SparsePolynomial.eval_scale, eval_atom1845]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1846 : SparsePolynomial.Poly := [([7,13,14], 1)]
theorem eval_atom1846 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1846 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom1846, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1846_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161349924489600 : Int) atom1846) := by
  rw [SparsePolynomial.eval_scale, eval_atom1846]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1847 : SparsePolynomial.Poly := [([7,13,15], 1)]
theorem eval_atom1847 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1847 = ((g 7) * (g 13) * (g 15)) := by
  norm_num [atom1847, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1847_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161456236233600 : Int) atom1847) := by
  rw [SparsePolynomial.eval_scale, eval_atom1847]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1848 : SparsePolynomial.Poly := [([7,13,16], 1)]
theorem eval_atom1848 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1848 = ((g 7) * (g 13) * (g 16)) := by
  norm_num [atom1848, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1848_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164645588553600 : Int) atom1848) := by
  rw [SparsePolynomial.eval_scale, eval_atom1848]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1849 : SparsePolynomial.Poly := [([7,13,17], 1)]
theorem eval_atom1849 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1849 = ((g 7) * (g 13) * (g 17)) := by
  norm_num [atom1849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1849_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167834940873600 : Int) atom1849) := by
  rw [SparsePolynomial.eval_scale, eval_atom1849]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1850 : SparsePolynomial.Poly := [([7,13,18], 1)]
theorem eval_atom1850 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1850 = ((g 7) * (g 13) * (g 18)) := by
  norm_num [atom1850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1850_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205428667012800 : Int) atom1850) := by
  rw [SparsePolynomial.eval_scale, eval_atom1850]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1851 : SparsePolynomial.Poly := [([7,13,19], 1)]
theorem eval_atom1851 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1851 = ((g 7) * (g 13) * (g 19)) := by
  norm_num [atom1851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1851_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198562752326400 : Int) atom1851) := by
  rw [SparsePolynomial.eval_scale, eval_atom1851]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1852 : SparsePolynomial.Poly := [([7,13,20], 1)]
theorem eval_atom1852 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1852 = ((g 7) * (g 13) * (g 20)) := by
  norm_num [atom1852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1852_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (303699386760000 : Int) atom1852) := by
  rw [SparsePolynomial.eval_scale, eval_atom1852]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1853 : SparsePolynomial.Poly := [([7,13,21], 1)]
theorem eval_atom1853 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1853 = ((g 7) * (g 13) * (g 21)) := by
  norm_num [atom1853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1853_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316161702780000 : Int) atom1853) := by
  rw [SparsePolynomial.eval_scale, eval_atom1853]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1854 : SparsePolynomial.Poly := [([7,13,22], 1)]
theorem eval_atom1854 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1854 = ((g 7) * (g 13) * (g 22)) := by
  norm_num [atom1854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1854_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (406002292080000 : Int) atom1854) := by
  rw [SparsePolynomial.eval_scale, eval_atom1854]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1855 : SparsePolynomial.Poly := [([7,13,23], 1)]
theorem eval_atom1855 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1855 = ((g 7) * (g 13) * (g 23)) := by
  norm_num [atom1855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1855_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (502095084598800 : Int) atom1855) := by
  rw [SparsePolynomial.eval_scale, eval_atom1855]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1856 : SparsePolynomial.Poly := [([7,14,14], 1)]
theorem eval_atom1856 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1856 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom1856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1856_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107957213548800 : Int) atom1856) := by
  rw [SparsePolynomial.eval_scale, eval_atom1856]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1857 : SparsePolynomial.Poly := [([7,14,15], 1)]
theorem eval_atom1857 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1857 = ((g 7) * (g 14) * (g 15)) := by
  norm_num [atom1857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1857_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207845365728000 : Int) atom1857) := by
  rw [SparsePolynomial.eval_scale, eval_atom1857]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1858 : SparsePolynomial.Poly := [([7,14,16], 1)]
theorem eval_atom1858 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1858 = ((g 7) * (g 14) * (g 16)) := by
  norm_num [atom1858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1858_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207994202169600 : Int) atom1858) := by
  rw [SparsePolynomial.eval_scale, eval_atom1858]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1859 : SparsePolynomial.Poly := [([7,14,17], 1)]
theorem eval_atom1859 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1859 = ((g 7) * (g 14) * (g 17)) := by
  norm_num [atom1859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1859_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208143038611200 : Int) atom1859) := by
  rw [SparsePolynomial.eval_scale, eval_atom1859]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1860 : SparsePolynomial.Poly := [([7,14,18], 1)]
theorem eval_atom1860 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1860 = ((g 7) * (g 14) * (g 18)) := by
  norm_num [atom1860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1860_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225112755436800 : Int) atom1860) := by
  rw [SparsePolynomial.eval_scale, eval_atom1860]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1861 : SparsePolynomial.Poly := [([7,14,19], 1)]
theorem eval_atom1861 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1861 = ((g 7) * (g 14) * (g 19)) := by
  norm_num [atom1861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1861_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226921383981600 : Int) atom1861) := by
  rw [SparsePolynomial.eval_scale, eval_atom1861]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1862 : SparsePolynomial.Poly := [([7,14,20], 1)]
theorem eval_atom1862 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1862 = ((g 7) * (g 14) * (g 20)) := by
  norm_num [atom1862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1862_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331289837894400 : Int) atom1862) := by
  rw [SparsePolynomial.eval_scale, eval_atom1862]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1863 : SparsePolynomial.Poly := [([7,14,21], 1)]
theorem eval_atom1863 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1863 = ((g 7) * (g 14) * (g 21)) := by
  norm_num [atom1863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1863_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349811115561600 : Int) atom1863) := by
  rw [SparsePolynomial.eval_scale, eval_atom1863]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1864 : SparsePolynomial.Poly := [([7,14,22], 1)]
theorem eval_atom1864 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1864 = ((g 7) * (g 14) * (g 22)) := by
  norm_num [atom1864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1864_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425331877740000 : Int) atom1864) := by
  rw [SparsePolynomial.eval_scale, eval_atom1864]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1865 : SparsePolynomial.Poly := [([7,14,23], 1)]
theorem eval_atom1865 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1865 = ((g 7) * (g 14) * (g 23)) := by
  norm_num [atom1865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1865_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (520737513357600 : Int) atom1865) := by
  rw [SparsePolynomial.eval_scale, eval_atom1865]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1866 : SparsePolynomial.Poly := [([7,15,15], 1)]
theorem eval_atom1866 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1866 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom1866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1866_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134822191257600 : Int) atom1866) := by
  rw [SparsePolynomial.eval_scale, eval_atom1866]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1867 : SparsePolynomial.Poly := [([7,15,16], 1)]
theorem eval_atom1867 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1867 = ((g 7) * (g 15) * (g 16)) := by
  norm_num [atom1867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1867_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (252379355289600 : Int) atom1867) := by
  rw [SparsePolynomial.eval_scale, eval_atom1867]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1868 : SparsePolynomial.Poly := [([7,15,17], 1)]
theorem eval_atom1868 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1868 = ((g 7) * (g 15) * (g 17)) := by
  norm_num [atom1868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1868_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (248467083110400 : Int) atom1868) := by
  rw [SparsePolynomial.eval_scale, eval_atom1868]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1869 : SparsePolynomial.Poly := [([7,15,18], 1)]
theorem eval_atom1869 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1869 = ((g 7) * (g 15) * (g 18)) := by
  norm_num [atom1869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1869_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266977353753600 : Int) atom1869) := by
  rw [SparsePolynomial.eval_scale, eval_atom1869]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1870 : SparsePolynomial.Poly := [([7,15,19], 1)]
theorem eval_atom1870 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1870 = ((g 7) * (g 15) * (g 19)) := by
  norm_num [atom1870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1870_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (260991680409600 : Int) atom1870) := by
  rw [SparsePolynomial.eval_scale, eval_atom1870]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1871 : SparsePolynomial.Poly := [([7,15,20], 1)]
theorem eval_atom1871 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1871 = ((g 7) * (g 15) * (g 20)) := by
  norm_num [atom1871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1871_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (395847805516800 : Int) atom1871) := by
  rw [SparsePolynomial.eval_scale, eval_atom1871]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1872 : SparsePolynomial.Poly := [([7,15,21], 1)]
theorem eval_atom1872 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1872 = ((g 7) * (g 15) * (g 21)) := by
  norm_num [atom1872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1872_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (424124796480000 : Int) atom1872) := by
  rw [SparsePolynomial.eval_scale, eval_atom1872]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1873 : SparsePolynomial.Poly := [([7,15,22], 1)]
theorem eval_atom1873 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1873 = ((g 7) * (g 15) * (g 22)) := by
  norm_num [atom1873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1873_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (438598012876800 : Int) atom1873) := by
  rw [SparsePolynomial.eval_scale, eval_atom1873]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1874 : SparsePolynomial.Poly := [([7,15,23], 1)]
theorem eval_atom1874 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1874 = ((g 7) * (g 15) * (g 23)) := by
  norm_num [atom1874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1874_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (529955345606400 : Int) atom1874) := by
  rw [SparsePolynomial.eval_scale, eval_atom1874]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1875 : SparsePolynomial.Poly := [([7,16,16], 1)]
theorem eval_atom1875 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1875 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom1875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1875_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155574243686400 : Int) atom1875) := by
  rw [SparsePolynomial.eval_scale, eval_atom1875]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1876 : SparsePolynomial.Poly := [([7,16,17], 1)]
theorem eval_atom1876 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1876 = ((g 7) * (g 16) * (g 17)) := by
  norm_num [atom1876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1876_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299071473254400 : Int) atom1876) := by
  rw [SparsePolynomial.eval_scale, eval_atom1876]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1877 : SparsePolynomial.Poly := [([7,16,18], 1)]
theorem eval_atom1877 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1877 = ((g 7) * (g 16) * (g 18)) := by
  norm_num [atom1877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1877_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291108186700800 : Int) atom1877) := by
  rw [SparsePolynomial.eval_scale, eval_atom1877]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1878 : SparsePolynomial.Poly := [([7,16,19], 1)]
theorem eval_atom1878 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1878 = ((g 7) * (g 16) * (g 19)) := by
  norm_num [atom1878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1878_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290557942886400 : Int) atom1878) := by
  rw [SparsePolynomial.eval_scale, eval_atom1878]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1879 : SparsePolynomial.Poly := [([7,16,20], 1)]
theorem eval_atom1879 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1879 = ((g 7) * (g 16) * (g 20)) := by
  norm_num [atom1879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1879_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (430849497523200 : Int) atom1879) := by
  rw [SparsePolynomial.eval_scale, eval_atom1879]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1880 : SparsePolynomial.Poly := [([7,16,21], 1)]
theorem eval_atom1880 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1880 = ((g 7) * (g 16) * (g 21)) := by
  norm_num [atom1880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1880_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (465926574220800 : Int) atom1880) := by
  rw [SparsePolynomial.eval_scale, eval_atom1880]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1881 : SparsePolynomial.Poly := [([7,16,22], 1)]
theorem eval_atom1881 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1881 = ((g 7) * (g 16) * (g 22)) := by
  norm_num [atom1881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1881_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (429406879372800 : Int) atom1881) := by
  rw [SparsePolynomial.eval_scale, eval_atom1881]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1882 : SparsePolynomial.Poly := [([7,16,23], 1)]
theorem eval_atom1882 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1882 = ((g 7) * (g 16) * (g 23)) := by
  norm_num [atom1882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1882_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (604781416915200 : Int) atom1882) := by
  rw [SparsePolynomial.eval_scale, eval_atom1882]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1883 : SparsePolynomial.Poly := [([7,17,17], 1)]
theorem eval_atom1883 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1883 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom1883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1883_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176723193292800 : Int) atom1883) := by
  rw [SparsePolynomial.eval_scale, eval_atom1883]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1884 : SparsePolynomial.Poly := [([7,17,18], 1)]
theorem eval_atom1884 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1884 = ((g 7) * (g 17) * (g 18)) := by
  norm_num [atom1884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1884_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330138127334400 : Int) atom1884) := by
  rw [SparsePolynomial.eval_scale, eval_atom1884]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1885 : SparsePolynomial.Poly := [([7,17,19], 1)]
theorem eval_atom1885 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1885 = ((g 7) * (g 17) * (g 19)) := by
  norm_num [atom1885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1885_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (339989682278400 : Int) atom1885) := by
  rw [SparsePolynomial.eval_scale, eval_atom1885]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1886 : SparsePolynomial.Poly := [([7,17,20], 1)]
theorem eval_atom1886 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1886 = ((g 7) * (g 17) * (g 20)) := by
  norm_num [atom1886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1886_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (490683035673600 : Int) atom1886) := by
  rw [SparsePolynomial.eval_scale, eval_atom1886]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1887 : SparsePolynomial.Poly := [([7,17,21], 1)]
theorem eval_atom1887 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1887 = ((g 7) * (g 17) * (g 21)) := by
  norm_num [atom1887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1887_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (535043382720000 : Int) atom1887) := by
  rw [SparsePolynomial.eval_scale, eval_atom1887]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1888 : SparsePolynomial.Poly := [([7,17,22], 1)]
theorem eval_atom1888 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1888 = ((g 7) * (g 17) * (g 22)) := by
  norm_num [atom1888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1888_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (506683275302400 : Int) atom1888) := by
  rw [SparsePolynomial.eval_scale, eval_atom1888]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block025 : SparsePolynomial.Poly := [([7,10,13], 46917379472304), ([7,10,14], 53104722973104), ([7,10,15], 59292066473904), ([7,10,16], 65479409974704), ([7,10,17], 71666753475504), ([7,10,18], 53145950625240), ([7,10,19], 60258778990080), ([7,10,20], 67371607354920), ([7,10,21], 150922586933052), ([7,10,22], 234473566511184), ([7,10,23], 330609990480858), ([7,11,11], 44798735335200), ([7,11,12], 72945064869600), ([7,11,13], 76070630143200), ([7,11,14], 79196195416800), ([7,11,15], 82321760690400), ([7,11,16], 88530366540000), ([7,11,17], 94738972389600), ([7,11,18], 100163032583856), ([7,11,19], 108467813667840), ([7,11,20], 138689388522960), ([7,11,21], 219887061777240), ([7,11,22], 311372780684064), ([7,11,23], 412496377316100), ([7,12,12], 59997328036800), ([7,12,13], 113390038977600), ([7,12,14], 118599314433600), ([7,12,15], 123808589889600), ([7,12,16], 129017865345600), ([7,12,17], 134227140801600), ([7,12,18], 180233184363936), ([7,12,19], 168555211376640), ([7,12,20], 266923278584160), ([7,12,21], 283378760863440), ([7,12,22], 369508560552384), ([7,12,23], 461296956166200), ([7,13,13], 85243709443200), ([7,13,14], 161349924489600), ([7,13,15], 161456236233600), ([7,13,16], 164645588553600), ([7,13,17], 167834940873600), ([7,13,18], 205428667012800), ([7,13,19], 198562752326400), ([7,13,20], 303699386760000), ([7,13,21], 316161702780000), ([7,13,22], 406002292080000), ([7,13,23], 502095084598800), ([7,14,14], 107957213548800), ([7,14,15], 207845365728000), ([7,14,16], 207994202169600), ([7,14,17], 208143038611200), ([7,14,18], 225112755436800), ([7,14,19], 226921383981600), ([7,14,20], 331289837894400), ([7,14,21], 349811115561600), ([7,14,22], 425331877740000), ([7,14,23], 520737513357600), ([7,15,15], 134822191257600), ([7,15,16], 252379355289600), ([7,15,17], 248467083110400), ([7,15,18], 266977353753600), ([7,15,19], 260991680409600), ([7,15,20], 395847805516800), ([7,15,21], 424124796480000), ([7,15,22], 438598012876800), ([7,15,23], 529955345606400), ([7,16,16], 155574243686400), ([7,16,17], 299071473254400), ([7,16,18], 291108186700800), ([7,16,19], 290557942886400), ([7,16,20], 430849497523200), ([7,16,21], 465926574220800), ([7,16,22], 429406879372800), ([7,16,23], 604781416915200), ([7,17,17], 176723193292800), ([7,17,18], 330138127334400), ([7,17,19], 339989682278400), ([7,17,20], 490683035673600), ([7,17,21], 535043382720000), ([7,17,22], 506683275302400)]
theorem block025_data : block025 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46917379472304 : Int) atom1809) (SparsePolynomial.scale (53104722973104 : Int) atom1810)) (SparsePolynomial.merge (SparsePolynomial.scale (59292066473904 : Int) atom1811) (SparsePolynomial.merge (SparsePolynomial.scale (65479409974704 : Int) atom1812) (SparsePolynomial.scale (71666753475504 : Int) atom1813)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (53145950625240 : Int) atom1814) (SparsePolynomial.scale (60258778990080 : Int) atom1815)) (SparsePolynomial.merge (SparsePolynomial.scale (67371607354920 : Int) atom1816) (SparsePolynomial.merge (SparsePolynomial.scale (150922586933052 : Int) atom1817) (SparsePolynomial.scale (234473566511184 : Int) atom1818))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (330609990480858 : Int) atom1819) (SparsePolynomial.scale (44798735335200 : Int) atom1820)) (SparsePolynomial.merge (SparsePolynomial.scale (72945064869600 : Int) atom1821) (SparsePolynomial.merge (SparsePolynomial.scale (76070630143200 : Int) atom1822) (SparsePolynomial.scale (79196195416800 : Int) atom1823)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (82321760690400 : Int) atom1824) (SparsePolynomial.scale (88530366540000 : Int) atom1825)) (SparsePolynomial.merge (SparsePolynomial.scale (94738972389600 : Int) atom1826) (SparsePolynomial.merge (SparsePolynomial.scale (100163032583856 : Int) atom1827) (SparsePolynomial.scale (108467813667840 : Int) atom1828)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (138689388522960 : Int) atom1829) (SparsePolynomial.scale (219887061777240 : Int) atom1830)) (SparsePolynomial.merge (SparsePolynomial.scale (311372780684064 : Int) atom1831) (SparsePolynomial.merge (SparsePolynomial.scale (412496377316100 : Int) atom1832) (SparsePolynomial.scale (59997328036800 : Int) atom1833)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (113390038977600 : Int) atom1834) (SparsePolynomial.scale (118599314433600 : Int) atom1835)) (SparsePolynomial.merge (SparsePolynomial.scale (123808589889600 : Int) atom1836) (SparsePolynomial.merge (SparsePolynomial.scale (129017865345600 : Int) atom1837) (SparsePolynomial.scale (134227140801600 : Int) atom1838))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (180233184363936 : Int) atom1839) (SparsePolynomial.scale (168555211376640 : Int) atom1840)) (SparsePolynomial.merge (SparsePolynomial.scale (266923278584160 : Int) atom1841) (SparsePolynomial.merge (SparsePolynomial.scale (283378760863440 : Int) atom1842) (SparsePolynomial.scale (369508560552384 : Int) atom1843)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (461296956166200 : Int) atom1844) (SparsePolynomial.scale (85243709443200 : Int) atom1845)) (SparsePolynomial.merge (SparsePolynomial.scale (161349924489600 : Int) atom1846) (SparsePolynomial.merge (SparsePolynomial.scale (161456236233600 : Int) atom1847) (SparsePolynomial.scale (164645588553600 : Int) atom1848))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (167834940873600 : Int) atom1849) (SparsePolynomial.scale (205428667012800 : Int) atom1850)) (SparsePolynomial.merge (SparsePolynomial.scale (198562752326400 : Int) atom1851) (SparsePolynomial.merge (SparsePolynomial.scale (303699386760000 : Int) atom1852) (SparsePolynomial.scale (316161702780000 : Int) atom1853)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (406002292080000 : Int) atom1854) (SparsePolynomial.scale (502095084598800 : Int) atom1855)) (SparsePolynomial.merge (SparsePolynomial.scale (107957213548800 : Int) atom1856) (SparsePolynomial.merge (SparsePolynomial.scale (207845365728000 : Int) atom1857) (SparsePolynomial.scale (207994202169600 : Int) atom1858))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (208143038611200 : Int) atom1859) (SparsePolynomial.scale (225112755436800 : Int) atom1860)) (SparsePolynomial.merge (SparsePolynomial.scale (226921383981600 : Int) atom1861) (SparsePolynomial.merge (SparsePolynomial.scale (331289837894400 : Int) atom1862) (SparsePolynomial.scale (349811115561600 : Int) atom1863)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (425331877740000 : Int) atom1864) (SparsePolynomial.scale (520737513357600 : Int) atom1865)) (SparsePolynomial.merge (SparsePolynomial.scale (134822191257600 : Int) atom1866) (SparsePolynomial.merge (SparsePolynomial.scale (252379355289600 : Int) atom1867) (SparsePolynomial.scale (248467083110400 : Int) atom1868)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (266977353753600 : Int) atom1869) (SparsePolynomial.scale (260991680409600 : Int) atom1870)) (SparsePolynomial.merge (SparsePolynomial.scale (395847805516800 : Int) atom1871) (SparsePolynomial.merge (SparsePolynomial.scale (424124796480000 : Int) atom1872) (SparsePolynomial.scale (438598012876800 : Int) atom1873)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (529955345606400 : Int) atom1874) (SparsePolynomial.scale (155574243686400 : Int) atom1875)) (SparsePolynomial.merge (SparsePolynomial.scale (299071473254400 : Int) atom1876) (SparsePolynomial.merge (SparsePolynomial.scale (291108186700800 : Int) atom1877) (SparsePolynomial.scale (290557942886400 : Int) atom1878))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (430849497523200 : Int) atom1879) (SparsePolynomial.scale (465926574220800 : Int) atom1880)) (SparsePolynomial.merge (SparsePolynomial.scale (429406879372800 : Int) atom1881) (SparsePolynomial.merge (SparsePolynomial.scale (604781416915200 : Int) atom1882) (SparsePolynomial.scale (176723193292800 : Int) atom1883)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (330138127334400 : Int) atom1884) (SparsePolynomial.scale (339989682278400 : Int) atom1885)) (SparsePolynomial.merge (SparsePolynomial.scale (490683035673600 : Int) atom1886) (SparsePolynomial.merge (SparsePolynomial.scale (535043382720000 : Int) atom1887) (SparsePolynomial.scale (506683275302400 : Int) atom1888)))))))) := by decide +kernel
theorem block025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block025 := by
  rw [block025_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1809_nonneg g hg hA hB) (atom1810_nonneg g hg hA hB)) (add_nonneg (atom1811_nonneg g hg hA hB) (add_nonneg (atom1812_nonneg g hg hA hB) (atom1813_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1814_nonneg g hg hA hB) (atom1815_nonneg g hg hA hB)) (add_nonneg (atom1816_nonneg g hg hA hB) (add_nonneg (atom1817_nonneg g hg hA hB) (atom1818_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1819_nonneg g hg hA hB) (atom1820_nonneg g hg hA hB)) (add_nonneg (atom1821_nonneg g hg hA hB) (add_nonneg (atom1822_nonneg g hg hA hB) (atom1823_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1824_nonneg g hg hA hB) (atom1825_nonneg g hg hA hB)) (add_nonneg (atom1826_nonneg g hg hA hB) (add_nonneg (atom1827_nonneg g hg hA hB) (atom1828_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1829_nonneg g hg hA hB) (atom1830_nonneg g hg hA hB)) (add_nonneg (atom1831_nonneg g hg hA hB) (add_nonneg (atom1832_nonneg g hg hA hB) (atom1833_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1834_nonneg g hg hA hB) (atom1835_nonneg g hg hA hB)) (add_nonneg (atom1836_nonneg g hg hA hB) (add_nonneg (atom1837_nonneg g hg hA hB) (atom1838_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1839_nonneg g hg hA hB) (atom1840_nonneg g hg hA hB)) (add_nonneg (atom1841_nonneg g hg hA hB) (add_nonneg (atom1842_nonneg g hg hA hB) (atom1843_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1844_nonneg g hg hA hB) (atom1845_nonneg g hg hA hB)) (add_nonneg (atom1846_nonneg g hg hA hB) (add_nonneg (atom1847_nonneg g hg hA hB) (atom1848_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1849_nonneg g hg hA hB) (atom1850_nonneg g hg hA hB)) (add_nonneg (atom1851_nonneg g hg hA hB) (add_nonneg (atom1852_nonneg g hg hA hB) (atom1853_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1854_nonneg g hg hA hB) (atom1855_nonneg g hg hA hB)) (add_nonneg (atom1856_nonneg g hg hA hB) (add_nonneg (atom1857_nonneg g hg hA hB) (atom1858_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1859_nonneg g hg hA hB) (atom1860_nonneg g hg hA hB)) (add_nonneg (atom1861_nonneg g hg hA hB) (add_nonneg (atom1862_nonneg g hg hA hB) (atom1863_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1864_nonneg g hg hA hB) (atom1865_nonneg g hg hA hB)) (add_nonneg (atom1866_nonneg g hg hA hB) (add_nonneg (atom1867_nonneg g hg hA hB) (atom1868_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1869_nonneg g hg hA hB) (atom1870_nonneg g hg hA hB)) (add_nonneg (atom1871_nonneg g hg hA hB) (add_nonneg (atom1872_nonneg g hg hA hB) (atom1873_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1874_nonneg g hg hA hB) (atom1875_nonneg g hg hA hB)) (add_nonneg (atom1876_nonneg g hg hA hB) (add_nonneg (atom1877_nonneg g hg hA hB) (atom1878_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1879_nonneg g hg hA hB) (atom1880_nonneg g hg hA hB)) (add_nonneg (atom1881_nonneg g hg hA hB) (add_nonneg (atom1882_nonneg g hg hA hB) (atom1883_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1884_nonneg g hg hA hB) (atom1885_nonneg g hg hA hB)) (add_nonneg (atom1886_nonneg g hg hA hB) (add_nonneg (atom1887_nonneg g hg hA hB) (atom1888_nonneg g hg hA hB))))))))

end APPT.Finite24
