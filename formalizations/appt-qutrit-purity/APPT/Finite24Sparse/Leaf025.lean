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
def atom1809Coded : CoefficientMerge.Poly := [(4285, 1)]
theorem atom1809Coded_decode : atom1809 = SparsePolynomial.decodeCubic 24 atom1809Coded := by decide +kernel
theorem atom1809Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46917379472304 : Int) atom1809Coded) := by
  have h := atom1809_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1809Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1810Coded : CoefficientMerge.Poly := [(4286, 1)]
theorem atom1810Coded_decode : atom1810 = SparsePolynomial.decodeCubic 24 atom1810Coded := by decide +kernel
theorem atom1810Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53104722973104 : Int) atom1810Coded) := by
  have h := atom1810_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1810Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1811Coded : CoefficientMerge.Poly := [(4287, 1)]
theorem atom1811Coded_decode : atom1811 = SparsePolynomial.decodeCubic 24 atom1811Coded := by decide +kernel
theorem atom1811Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59292066473904 : Int) atom1811Coded) := by
  have h := atom1811_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1811Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1812Coded : CoefficientMerge.Poly := [(4288, 1)]
theorem atom1812Coded_decode : atom1812 = SparsePolynomial.decodeCubic 24 atom1812Coded := by decide +kernel
theorem atom1812Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65479409974704 : Int) atom1812Coded) := by
  have h := atom1812_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1812Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1813Coded : CoefficientMerge.Poly := [(4289, 1)]
theorem atom1813Coded_decode : atom1813 = SparsePolynomial.decodeCubic 24 atom1813Coded := by decide +kernel
theorem atom1813Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71666753475504 : Int) atom1813Coded) := by
  have h := atom1813_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1813Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1814Coded : CoefficientMerge.Poly := [(4290, 1)]
theorem atom1814Coded_decode : atom1814 = SparsePolynomial.decodeCubic 24 atom1814Coded := by decide +kernel
theorem atom1814Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53145950625240 : Int) atom1814Coded) := by
  have h := atom1814_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1814Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1815Coded : CoefficientMerge.Poly := [(4291, 1)]
theorem atom1815Coded_decode : atom1815 = SparsePolynomial.decodeCubic 24 atom1815Coded := by decide +kernel
theorem atom1815Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60258778990080 : Int) atom1815Coded) := by
  have h := atom1815_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1815Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1816Coded : CoefficientMerge.Poly := [(4292, 1)]
theorem atom1816Coded_decode : atom1816 = SparsePolynomial.decodeCubic 24 atom1816Coded := by decide +kernel
theorem atom1816Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (67371607354920 : Int) atom1816Coded) := by
  have h := atom1816_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1816Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1817Coded : CoefficientMerge.Poly := [(4293, 1)]
theorem atom1817Coded_decode : atom1817 = SparsePolynomial.decodeCubic 24 atom1817Coded := by decide +kernel
theorem atom1817Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150922586933052 : Int) atom1817Coded) := by
  have h := atom1817_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1817Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1818Coded : CoefficientMerge.Poly := [(4294, 1)]
theorem atom1818Coded_decode : atom1818 = SparsePolynomial.decodeCubic 24 atom1818Coded := by decide +kernel
theorem atom1818Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (234473566511184 : Int) atom1818Coded) := by
  have h := atom1818_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1818Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1819Coded : CoefficientMerge.Poly := [(4295, 1)]
theorem atom1819Coded_decode : atom1819 = SparsePolynomial.decodeCubic 24 atom1819Coded := by decide +kernel
theorem atom1819Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (330609990480858 : Int) atom1819Coded) := by
  have h := atom1819_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1819Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1820Coded : CoefficientMerge.Poly := [(4307, 1)]
theorem atom1820Coded_decode : atom1820 = SparsePolynomial.decodeCubic 24 atom1820Coded := by decide +kernel
theorem atom1820Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (44798735335200 : Int) atom1820Coded) := by
  have h := atom1820_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1820Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1821Coded : CoefficientMerge.Poly := [(4308, 1)]
theorem atom1821Coded_decode : atom1821 = SparsePolynomial.decodeCubic 24 atom1821Coded := by decide +kernel
theorem atom1821Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72945064869600 : Int) atom1821Coded) := by
  have h := atom1821_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1821Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1822Coded : CoefficientMerge.Poly := [(4309, 1)]
theorem atom1822Coded_decode : atom1822 = SparsePolynomial.decodeCubic 24 atom1822Coded := by decide +kernel
theorem atom1822Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (76070630143200 : Int) atom1822Coded) := by
  have h := atom1822_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1822Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1823Coded : CoefficientMerge.Poly := [(4310, 1)]
theorem atom1823Coded_decode : atom1823 = SparsePolynomial.decodeCubic 24 atom1823Coded := by decide +kernel
theorem atom1823Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79196195416800 : Int) atom1823Coded) := by
  have h := atom1823_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1823Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1824Coded : CoefficientMerge.Poly := [(4311, 1)]
theorem atom1824Coded_decode : atom1824 = SparsePolynomial.decodeCubic 24 atom1824Coded := by decide +kernel
theorem atom1824Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (82321760690400 : Int) atom1824Coded) := by
  have h := atom1824_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1824Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1825Coded : CoefficientMerge.Poly := [(4312, 1)]
theorem atom1825Coded_decode : atom1825 = SparsePolynomial.decodeCubic 24 atom1825Coded := by decide +kernel
theorem atom1825Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88530366540000 : Int) atom1825Coded) := by
  have h := atom1825_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1825Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1826Coded : CoefficientMerge.Poly := [(4313, 1)]
theorem atom1826Coded_decode : atom1826 = SparsePolynomial.decodeCubic 24 atom1826Coded := by decide +kernel
theorem atom1826Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (94738972389600 : Int) atom1826Coded) := by
  have h := atom1826_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1826Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1827Coded : CoefficientMerge.Poly := [(4314, 1)]
theorem atom1827Coded_decode : atom1827 = SparsePolynomial.decodeCubic 24 atom1827Coded := by decide +kernel
theorem atom1827Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100163032583856 : Int) atom1827Coded) := by
  have h := atom1827_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1827Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1828Coded : CoefficientMerge.Poly := [(4315, 1)]
theorem atom1828Coded_decode : atom1828 = SparsePolynomial.decodeCubic 24 atom1828Coded := by decide +kernel
theorem atom1828Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108467813667840 : Int) atom1828Coded) := by
  have h := atom1828_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1828Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1829Coded : CoefficientMerge.Poly := [(4316, 1)]
theorem atom1829Coded_decode : atom1829 = SparsePolynomial.decodeCubic 24 atom1829Coded := by decide +kernel
theorem atom1829Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (138689388522960 : Int) atom1829Coded) := by
  have h := atom1829_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1829Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1830Coded : CoefficientMerge.Poly := [(4317, 1)]
theorem atom1830Coded_decode : atom1830 = SparsePolynomial.decodeCubic 24 atom1830Coded := by decide +kernel
theorem atom1830Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (219887061777240 : Int) atom1830Coded) := by
  have h := atom1830_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1830Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1831Coded : CoefficientMerge.Poly := [(4318, 1)]
theorem atom1831Coded_decode : atom1831 = SparsePolynomial.decodeCubic 24 atom1831Coded := by decide +kernel
theorem atom1831Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (311372780684064 : Int) atom1831Coded) := by
  have h := atom1831_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1831Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1832Coded : CoefficientMerge.Poly := [(4319, 1)]
theorem atom1832Coded_decode : atom1832 = SparsePolynomial.decodeCubic 24 atom1832Coded := by decide +kernel
theorem atom1832Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (412496377316100 : Int) atom1832Coded) := by
  have h := atom1832_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1832Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1833Coded : CoefficientMerge.Poly := [(4332, 1)]
theorem atom1833Coded_decode : atom1833 = SparsePolynomial.decodeCubic 24 atom1833Coded := by decide +kernel
theorem atom1833Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59997328036800 : Int) atom1833Coded) := by
  have h := atom1833_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1833Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1834Coded : CoefficientMerge.Poly := [(4333, 1)]
theorem atom1834Coded_decode : atom1834 = SparsePolynomial.decodeCubic 24 atom1834Coded := by decide +kernel
theorem atom1834Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (113390038977600 : Int) atom1834Coded) := by
  have h := atom1834_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1834Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1835Coded : CoefficientMerge.Poly := [(4334, 1)]
theorem atom1835Coded_decode : atom1835 = SparsePolynomial.decodeCubic 24 atom1835Coded := by decide +kernel
theorem atom1835Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118599314433600 : Int) atom1835Coded) := by
  have h := atom1835_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1835Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1836Coded : CoefficientMerge.Poly := [(4335, 1)]
theorem atom1836Coded_decode : atom1836 = SparsePolynomial.decodeCubic 24 atom1836Coded := by decide +kernel
theorem atom1836Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123808589889600 : Int) atom1836Coded) := by
  have h := atom1836_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1836Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1837Coded : CoefficientMerge.Poly := [(4336, 1)]
theorem atom1837Coded_decode : atom1837 = SparsePolynomial.decodeCubic 24 atom1837Coded := by decide +kernel
theorem atom1837Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129017865345600 : Int) atom1837Coded) := by
  have h := atom1837_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1837Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1838Coded : CoefficientMerge.Poly := [(4337, 1)]
theorem atom1838Coded_decode : atom1838 = SparsePolynomial.decodeCubic 24 atom1838Coded := by decide +kernel
theorem atom1838Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134227140801600 : Int) atom1838Coded) := by
  have h := atom1838_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1838Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1839Coded : CoefficientMerge.Poly := [(4338, 1)]
theorem atom1839Coded_decode : atom1839 = SparsePolynomial.decodeCubic 24 atom1839Coded := by decide +kernel
theorem atom1839Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (180233184363936 : Int) atom1839Coded) := by
  have h := atom1839_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1839Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1840Coded : CoefficientMerge.Poly := [(4339, 1)]
theorem atom1840Coded_decode : atom1840 = SparsePolynomial.decodeCubic 24 atom1840Coded := by decide +kernel
theorem atom1840Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168555211376640 : Int) atom1840Coded) := by
  have h := atom1840_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1840Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1841Coded : CoefficientMerge.Poly := [(4340, 1)]
theorem atom1841Coded_decode : atom1841 = SparsePolynomial.decodeCubic 24 atom1841Coded := by decide +kernel
theorem atom1841Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266923278584160 : Int) atom1841Coded) := by
  have h := atom1841_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1841Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1842Coded : CoefficientMerge.Poly := [(4341, 1)]
theorem atom1842Coded_decode : atom1842 = SparsePolynomial.decodeCubic 24 atom1842Coded := by decide +kernel
theorem atom1842Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283378760863440 : Int) atom1842Coded) := by
  have h := atom1842_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1842Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1843Coded : CoefficientMerge.Poly := [(4342, 1)]
theorem atom1843Coded_decode : atom1843 = SparsePolynomial.decodeCubic 24 atom1843Coded := by decide +kernel
theorem atom1843Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (369508560552384 : Int) atom1843Coded) := by
  have h := atom1843_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1843Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1844Coded : CoefficientMerge.Poly := [(4343, 1)]
theorem atom1844Coded_decode : atom1844 = SparsePolynomial.decodeCubic 24 atom1844Coded := by decide +kernel
theorem atom1844Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461296956166200 : Int) atom1844Coded) := by
  have h := atom1844_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1844Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1845Coded : CoefficientMerge.Poly := [(4357, 1)]
theorem atom1845Coded_decode : atom1845 = SparsePolynomial.decodeCubic 24 atom1845Coded := by decide +kernel
theorem atom1845Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85243709443200 : Int) atom1845Coded) := by
  have h := atom1845_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1845Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1846Coded : CoefficientMerge.Poly := [(4358, 1)]
theorem atom1846Coded_decode : atom1846 = SparsePolynomial.decodeCubic 24 atom1846Coded := by decide +kernel
theorem atom1846Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161349924489600 : Int) atom1846Coded) := by
  have h := atom1846_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1846Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1847Coded : CoefficientMerge.Poly := [(4359, 1)]
theorem atom1847Coded_decode : atom1847 = SparsePolynomial.decodeCubic 24 atom1847Coded := by decide +kernel
theorem atom1847Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161456236233600 : Int) atom1847Coded) := by
  have h := atom1847_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1847Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1848Coded : CoefficientMerge.Poly := [(4360, 1)]
theorem atom1848Coded_decode : atom1848 = SparsePolynomial.decodeCubic 24 atom1848Coded := by decide +kernel
theorem atom1848Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164645588553600 : Int) atom1848Coded) := by
  have h := atom1848_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1848Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1849Coded : CoefficientMerge.Poly := [(4361, 1)]
theorem atom1849Coded_decode : atom1849 = SparsePolynomial.decodeCubic 24 atom1849Coded := by decide +kernel
theorem atom1849Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167834940873600 : Int) atom1849Coded) := by
  have h := atom1849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1850Coded : CoefficientMerge.Poly := [(4362, 1)]
theorem atom1850Coded_decode : atom1850 = SparsePolynomial.decodeCubic 24 atom1850Coded := by decide +kernel
theorem atom1850Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205428667012800 : Int) atom1850Coded) := by
  have h := atom1850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1851Coded : CoefficientMerge.Poly := [(4363, 1)]
theorem atom1851Coded_decode : atom1851 = SparsePolynomial.decodeCubic 24 atom1851Coded := by decide +kernel
theorem atom1851Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (198562752326400 : Int) atom1851Coded) := by
  have h := atom1851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1852Coded : CoefficientMerge.Poly := [(4364, 1)]
theorem atom1852Coded_decode : atom1852 = SparsePolynomial.decodeCubic 24 atom1852Coded := by decide +kernel
theorem atom1852Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (303699386760000 : Int) atom1852Coded) := by
  have h := atom1852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1853Coded : CoefficientMerge.Poly := [(4365, 1)]
theorem atom1853Coded_decode : atom1853 = SparsePolynomial.decodeCubic 24 atom1853Coded := by decide +kernel
theorem atom1853Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316161702780000 : Int) atom1853Coded) := by
  have h := atom1853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1854Coded : CoefficientMerge.Poly := [(4366, 1)]
theorem atom1854Coded_decode : atom1854 = SparsePolynomial.decodeCubic 24 atom1854Coded := by decide +kernel
theorem atom1854Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (406002292080000 : Int) atom1854Coded) := by
  have h := atom1854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1855Coded : CoefficientMerge.Poly := [(4367, 1)]
theorem atom1855Coded_decode : atom1855 = SparsePolynomial.decodeCubic 24 atom1855Coded := by decide +kernel
theorem atom1855Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (502095084598800 : Int) atom1855Coded) := by
  have h := atom1855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1856Coded : CoefficientMerge.Poly := [(4382, 1)]
theorem atom1856Coded_decode : atom1856 = SparsePolynomial.decodeCubic 24 atom1856Coded := by decide +kernel
theorem atom1856Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107957213548800 : Int) atom1856Coded) := by
  have h := atom1856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1857Coded : CoefficientMerge.Poly := [(4383, 1)]
theorem atom1857Coded_decode : atom1857 = SparsePolynomial.decodeCubic 24 atom1857Coded := by decide +kernel
theorem atom1857Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207845365728000 : Int) atom1857Coded) := by
  have h := atom1857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1858Coded : CoefficientMerge.Poly := [(4384, 1)]
theorem atom1858Coded_decode : atom1858 = SparsePolynomial.decodeCubic 24 atom1858Coded := by decide +kernel
theorem atom1858Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207994202169600 : Int) atom1858Coded) := by
  have h := atom1858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1859Coded : CoefficientMerge.Poly := [(4385, 1)]
theorem atom1859Coded_decode : atom1859 = SparsePolynomial.decodeCubic 24 atom1859Coded := by decide +kernel
theorem atom1859Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208143038611200 : Int) atom1859Coded) := by
  have h := atom1859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1860Coded : CoefficientMerge.Poly := [(4386, 1)]
theorem atom1860Coded_decode : atom1860 = SparsePolynomial.decodeCubic 24 atom1860Coded := by decide +kernel
theorem atom1860Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225112755436800 : Int) atom1860Coded) := by
  have h := atom1860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1861Coded : CoefficientMerge.Poly := [(4387, 1)]
theorem atom1861Coded_decode : atom1861 = SparsePolynomial.decodeCubic 24 atom1861Coded := by decide +kernel
theorem atom1861Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226921383981600 : Int) atom1861Coded) := by
  have h := atom1861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1862Coded : CoefficientMerge.Poly := [(4388, 1)]
theorem atom1862Coded_decode : atom1862 = SparsePolynomial.decodeCubic 24 atom1862Coded := by decide +kernel
theorem atom1862Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (331289837894400 : Int) atom1862Coded) := by
  have h := atom1862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1863Coded : CoefficientMerge.Poly := [(4389, 1)]
theorem atom1863Coded_decode : atom1863 = SparsePolynomial.decodeCubic 24 atom1863Coded := by decide +kernel
theorem atom1863Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349811115561600 : Int) atom1863Coded) := by
  have h := atom1863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1864Coded : CoefficientMerge.Poly := [(4390, 1)]
theorem atom1864Coded_decode : atom1864 = SparsePolynomial.decodeCubic 24 atom1864Coded := by decide +kernel
theorem atom1864Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (425331877740000 : Int) atom1864Coded) := by
  have h := atom1864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1865Coded : CoefficientMerge.Poly := [(4391, 1)]
theorem atom1865Coded_decode : atom1865 = SparsePolynomial.decodeCubic 24 atom1865Coded := by decide +kernel
theorem atom1865Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (520737513357600 : Int) atom1865Coded) := by
  have h := atom1865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1866Coded : CoefficientMerge.Poly := [(4407, 1)]
theorem atom1866Coded_decode : atom1866 = SparsePolynomial.decodeCubic 24 atom1866Coded := by decide +kernel
theorem atom1866Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134822191257600 : Int) atom1866Coded) := by
  have h := atom1866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1867Coded : CoefficientMerge.Poly := [(4408, 1)]
theorem atom1867Coded_decode : atom1867 = SparsePolynomial.decodeCubic 24 atom1867Coded := by decide +kernel
theorem atom1867Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (252379355289600 : Int) atom1867Coded) := by
  have h := atom1867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1868Coded : CoefficientMerge.Poly := [(4409, 1)]
theorem atom1868Coded_decode : atom1868 = SparsePolynomial.decodeCubic 24 atom1868Coded := by decide +kernel
theorem atom1868Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (248467083110400 : Int) atom1868Coded) := by
  have h := atom1868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1869Coded : CoefficientMerge.Poly := [(4410, 1)]
theorem atom1869Coded_decode : atom1869 = SparsePolynomial.decodeCubic 24 atom1869Coded := by decide +kernel
theorem atom1869Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266977353753600 : Int) atom1869Coded) := by
  have h := atom1869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1870Coded : CoefficientMerge.Poly := [(4411, 1)]
theorem atom1870Coded_decode : atom1870 = SparsePolynomial.decodeCubic 24 atom1870Coded := by decide +kernel
theorem atom1870Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (260991680409600 : Int) atom1870Coded) := by
  have h := atom1870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1871Coded : CoefficientMerge.Poly := [(4412, 1)]
theorem atom1871Coded_decode : atom1871 = SparsePolynomial.decodeCubic 24 atom1871Coded := by decide +kernel
theorem atom1871Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (395847805516800 : Int) atom1871Coded) := by
  have h := atom1871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1872Coded : CoefficientMerge.Poly := [(4413, 1)]
theorem atom1872Coded_decode : atom1872 = SparsePolynomial.decodeCubic 24 atom1872Coded := by decide +kernel
theorem atom1872Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (424124796480000 : Int) atom1872Coded) := by
  have h := atom1872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1873Coded : CoefficientMerge.Poly := [(4414, 1)]
theorem atom1873Coded_decode : atom1873 = SparsePolynomial.decodeCubic 24 atom1873Coded := by decide +kernel
theorem atom1873Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (438598012876800 : Int) atom1873Coded) := by
  have h := atom1873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1874Coded : CoefficientMerge.Poly := [(4415, 1)]
theorem atom1874Coded_decode : atom1874 = SparsePolynomial.decodeCubic 24 atom1874Coded := by decide +kernel
theorem atom1874Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (529955345606400 : Int) atom1874Coded) := by
  have h := atom1874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1875Coded : CoefficientMerge.Poly := [(4432, 1)]
theorem atom1875Coded_decode : atom1875 = SparsePolynomial.decodeCubic 24 atom1875Coded := by decide +kernel
theorem atom1875Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155574243686400 : Int) atom1875Coded) := by
  have h := atom1875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1876Coded : CoefficientMerge.Poly := [(4433, 1)]
theorem atom1876Coded_decode : atom1876 = SparsePolynomial.decodeCubic 24 atom1876Coded := by decide +kernel
theorem atom1876Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299071473254400 : Int) atom1876Coded) := by
  have h := atom1876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1877Coded : CoefficientMerge.Poly := [(4434, 1)]
theorem atom1877Coded_decode : atom1877 = SparsePolynomial.decodeCubic 24 atom1877Coded := by decide +kernel
theorem atom1877Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291108186700800 : Int) atom1877Coded) := by
  have h := atom1877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1878Coded : CoefficientMerge.Poly := [(4435, 1)]
theorem atom1878Coded_decode : atom1878 = SparsePolynomial.decodeCubic 24 atom1878Coded := by decide +kernel
theorem atom1878Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (290557942886400 : Int) atom1878Coded) := by
  have h := atom1878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1879Coded : CoefficientMerge.Poly := [(4436, 1)]
theorem atom1879Coded_decode : atom1879 = SparsePolynomial.decodeCubic 24 atom1879Coded := by decide +kernel
theorem atom1879Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (430849497523200 : Int) atom1879Coded) := by
  have h := atom1879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1880Coded : CoefficientMerge.Poly := [(4437, 1)]
theorem atom1880Coded_decode : atom1880 = SparsePolynomial.decodeCubic 24 atom1880Coded := by decide +kernel
theorem atom1880Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (465926574220800 : Int) atom1880Coded) := by
  have h := atom1880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1881Coded : CoefficientMerge.Poly := [(4438, 1)]
theorem atom1881Coded_decode : atom1881 = SparsePolynomial.decodeCubic 24 atom1881Coded := by decide +kernel
theorem atom1881Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (429406879372800 : Int) atom1881Coded) := by
  have h := atom1881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1882Coded : CoefficientMerge.Poly := [(4439, 1)]
theorem atom1882Coded_decode : atom1882 = SparsePolynomial.decodeCubic 24 atom1882Coded := by decide +kernel
theorem atom1882Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (604781416915200 : Int) atom1882Coded) := by
  have h := atom1882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1883Coded : CoefficientMerge.Poly := [(4457, 1)]
theorem atom1883Coded_decode : atom1883 = SparsePolynomial.decodeCubic 24 atom1883Coded := by decide +kernel
theorem atom1883Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176723193292800 : Int) atom1883Coded) := by
  have h := atom1883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1884Coded : CoefficientMerge.Poly := [(4458, 1)]
theorem atom1884Coded_decode : atom1884 = SparsePolynomial.decodeCubic 24 atom1884Coded := by decide +kernel
theorem atom1884Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (330138127334400 : Int) atom1884Coded) := by
  have h := atom1884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1885Coded : CoefficientMerge.Poly := [(4459, 1)]
theorem atom1885Coded_decode : atom1885 = SparsePolynomial.decodeCubic 24 atom1885Coded := by decide +kernel
theorem atom1885Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339989682278400 : Int) atom1885Coded) := by
  have h := atom1885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1886Coded : CoefficientMerge.Poly := [(4460, 1)]
theorem atom1886Coded_decode : atom1886 = SparsePolynomial.decodeCubic 24 atom1886Coded := by decide +kernel
theorem atom1886Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (490683035673600 : Int) atom1886Coded) := by
  have h := atom1886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1887Coded : CoefficientMerge.Poly := [(4461, 1)]
theorem atom1887Coded_decode : atom1887 = SparsePolynomial.decodeCubic 24 atom1887Coded := by decide +kernel
theorem atom1887Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (535043382720000 : Int) atom1887Coded) := by
  have h := atom1887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
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
def atom1888Coded : CoefficientMerge.Poly := [(4462, 1)]
theorem atom1888Coded_decode : atom1888 = SparsePolynomial.decodeCubic 24 atom1888Coded := by decide +kernel
theorem atom1888Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (506683275302400 : Int) atom1888Coded) := by
  have h := atom1888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block025 : CoefficientMerge.Poly := [(4285, 46917379472304), (4286, 53104722973104), (4287, 59292066473904), (4288, 65479409974704), (4289, 71666753475504), (4290, 53145950625240), (4291, 60258778990080), (4292, 67371607354920), (4293, 150922586933052), (4294, 234473566511184), (4295, 330609990480858), (4307, 44798735335200), (4308, 72945064869600), (4309, 76070630143200), (4310, 79196195416800), (4311, 82321760690400), (4312, 88530366540000), (4313, 94738972389600), (4314, 100163032583856), (4315, 108467813667840), (4316, 138689388522960), (4317, 219887061777240), (4318, 311372780684064), (4319, 412496377316100), (4332, 59997328036800), (4333, 113390038977600), (4334, 118599314433600), (4335, 123808589889600), (4336, 129017865345600), (4337, 134227140801600), (4338, 180233184363936), (4339, 168555211376640), (4340, 266923278584160), (4341, 283378760863440), (4342, 369508560552384), (4343, 461296956166200), (4357, 85243709443200), (4358, 161349924489600), (4359, 161456236233600), (4360, 164645588553600), (4361, 167834940873600), (4362, 205428667012800), (4363, 198562752326400), (4364, 303699386760000), (4365, 316161702780000), (4366, 406002292080000), (4367, 502095084598800), (4382, 107957213548800), (4383, 207845365728000), (4384, 207994202169600), (4385, 208143038611200), (4386, 225112755436800), (4387, 226921383981600), (4388, 331289837894400), (4389, 349811115561600), (4390, 425331877740000), (4391, 520737513357600), (4407, 134822191257600), (4408, 252379355289600), (4409, 248467083110400), (4410, 266977353753600), (4411, 260991680409600), (4412, 395847805516800), (4413, 424124796480000), (4414, 438598012876800), (4415, 529955345606400), (4432, 155574243686400), (4433, 299071473254400), (4434, 291108186700800), (4435, 290557942886400), (4436, 430849497523200), (4437, 465926574220800), (4438, 429406879372800), (4439, 604781416915200), (4457, 176723193292800), (4458, 330138127334400), (4459, 339989682278400), (4460, 490683035673600), (4461, 535043382720000), (4462, 506683275302400)]
theorem block025_data : block025 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46917379472304 : Int) atom1809Coded) (CoefficientMerge.scale (53104722973104 : Int) atom1810Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59292066473904 : Int) atom1811Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65479409974704 : Int) atom1812Coded) (CoefficientMerge.scale (71666753475504 : Int) atom1813Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53145950625240 : Int) atom1814Coded) (CoefficientMerge.scale (60258778990080 : Int) atom1815Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67371607354920 : Int) atom1816Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150922586933052 : Int) atom1817Coded) (CoefficientMerge.scale (234473566511184 : Int) atom1818Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330609990480858 : Int) atom1819Coded) (CoefficientMerge.scale (44798735335200 : Int) atom1820Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (72945064869600 : Int) atom1821Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76070630143200 : Int) atom1822Coded) (CoefficientMerge.scale (79196195416800 : Int) atom1823Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82321760690400 : Int) atom1824Coded) (CoefficientMerge.scale (88530366540000 : Int) atom1825Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94738972389600 : Int) atom1826Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (100163032583856 : Int) atom1827Coded) (CoefficientMerge.scale (108467813667840 : Int) atom1828Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (138689388522960 : Int) atom1829Coded) (CoefficientMerge.scale (219887061777240 : Int) atom1830Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311372780684064 : Int) atom1831Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (412496377316100 : Int) atom1832Coded) (CoefficientMerge.scale (59997328036800 : Int) atom1833Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (113390038977600 : Int) atom1834Coded) (CoefficientMerge.scale (118599314433600 : Int) atom1835Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (123808589889600 : Int) atom1836Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129017865345600 : Int) atom1837Coded) (CoefficientMerge.scale (134227140801600 : Int) atom1838Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180233184363936 : Int) atom1839Coded) (CoefficientMerge.scale (168555211376640 : Int) atom1840Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (266923278584160 : Int) atom1841Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283378760863440 : Int) atom1842Coded) (CoefficientMerge.scale (369508560552384 : Int) atom1843Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (461296956166200 : Int) atom1844Coded) (CoefficientMerge.scale (85243709443200 : Int) atom1845Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161349924489600 : Int) atom1846Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161456236233600 : Int) atom1847Coded) (CoefficientMerge.scale (164645588553600 : Int) atom1848Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167834940873600 : Int) atom1849Coded) (CoefficientMerge.scale (205428667012800 : Int) atom1850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (198562752326400 : Int) atom1851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (303699386760000 : Int) atom1852Coded) (CoefficientMerge.scale (316161702780000 : Int) atom1853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (406002292080000 : Int) atom1854Coded) (CoefficientMerge.scale (502095084598800 : Int) atom1855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107957213548800 : Int) atom1856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207845365728000 : Int) atom1857Coded) (CoefficientMerge.scale (207994202169600 : Int) atom1858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208143038611200 : Int) atom1859Coded) (CoefficientMerge.scale (225112755436800 : Int) atom1860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226921383981600 : Int) atom1861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331289837894400 : Int) atom1862Coded) (CoefficientMerge.scale (349811115561600 : Int) atom1863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (425331877740000 : Int) atom1864Coded) (CoefficientMerge.scale (520737513357600 : Int) atom1865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134822191257600 : Int) atom1866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (252379355289600 : Int) atom1867Coded) (CoefficientMerge.scale (248467083110400 : Int) atom1868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (266977353753600 : Int) atom1869Coded) (CoefficientMerge.scale (260991680409600 : Int) atom1870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (395847805516800 : Int) atom1871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424124796480000 : Int) atom1872Coded) (CoefficientMerge.scale (438598012876800 : Int) atom1873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (529955345606400 : Int) atom1874Coded) (CoefficientMerge.scale (155574243686400 : Int) atom1875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299071473254400 : Int) atom1876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291108186700800 : Int) atom1877Coded) (CoefficientMerge.scale (290557942886400 : Int) atom1878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (430849497523200 : Int) atom1879Coded) (CoefficientMerge.scale (465926574220800 : Int) atom1880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (429406879372800 : Int) atom1881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (604781416915200 : Int) atom1882Coded) (CoefficientMerge.scale (176723193292800 : Int) atom1883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330138127334400 : Int) atom1884Coded) (CoefficientMerge.scale (339989682278400 : Int) atom1885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490683035673600 : Int) atom1886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (535043382720000 : Int) atom1887Coded) (CoefficientMerge.scale (506683275302400 : Int) atom1888Coded)))))))) := by decide +kernel
theorem block025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block025 := by
  rw [block025_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1809Coded_nonneg g hg hA hB) (atom1810Coded_nonneg g hg hA hB)) (add_nonneg (atom1811Coded_nonneg g hg hA hB) (add_nonneg (atom1812Coded_nonneg g hg hA hB) (atom1813Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1814Coded_nonneg g hg hA hB) (atom1815Coded_nonneg g hg hA hB)) (add_nonneg (atom1816Coded_nonneg g hg hA hB) (add_nonneg (atom1817Coded_nonneg g hg hA hB) (atom1818Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1819Coded_nonneg g hg hA hB) (atom1820Coded_nonneg g hg hA hB)) (add_nonneg (atom1821Coded_nonneg g hg hA hB) (add_nonneg (atom1822Coded_nonneg g hg hA hB) (atom1823Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1824Coded_nonneg g hg hA hB) (atom1825Coded_nonneg g hg hA hB)) (add_nonneg (atom1826Coded_nonneg g hg hA hB) (add_nonneg (atom1827Coded_nonneg g hg hA hB) (atom1828Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1829Coded_nonneg g hg hA hB) (atom1830Coded_nonneg g hg hA hB)) (add_nonneg (atom1831Coded_nonneg g hg hA hB) (add_nonneg (atom1832Coded_nonneg g hg hA hB) (atom1833Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1834Coded_nonneg g hg hA hB) (atom1835Coded_nonneg g hg hA hB)) (add_nonneg (atom1836Coded_nonneg g hg hA hB) (add_nonneg (atom1837Coded_nonneg g hg hA hB) (atom1838Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1839Coded_nonneg g hg hA hB) (atom1840Coded_nonneg g hg hA hB)) (add_nonneg (atom1841Coded_nonneg g hg hA hB) (add_nonneg (atom1842Coded_nonneg g hg hA hB) (atom1843Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1844Coded_nonneg g hg hA hB) (atom1845Coded_nonneg g hg hA hB)) (add_nonneg (atom1846Coded_nonneg g hg hA hB) (add_nonneg (atom1847Coded_nonneg g hg hA hB) (atom1848Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1849Coded_nonneg g hg hA hB) (atom1850Coded_nonneg g hg hA hB)) (add_nonneg (atom1851Coded_nonneg g hg hA hB) (add_nonneg (atom1852Coded_nonneg g hg hA hB) (atom1853Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1854Coded_nonneg g hg hA hB) (atom1855Coded_nonneg g hg hA hB)) (add_nonneg (atom1856Coded_nonneg g hg hA hB) (add_nonneg (atom1857Coded_nonneg g hg hA hB) (atom1858Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1859Coded_nonneg g hg hA hB) (atom1860Coded_nonneg g hg hA hB)) (add_nonneg (atom1861Coded_nonneg g hg hA hB) (add_nonneg (atom1862Coded_nonneg g hg hA hB) (atom1863Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1864Coded_nonneg g hg hA hB) (atom1865Coded_nonneg g hg hA hB)) (add_nonneg (atom1866Coded_nonneg g hg hA hB) (add_nonneg (atom1867Coded_nonneg g hg hA hB) (atom1868Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1869Coded_nonneg g hg hA hB) (atom1870Coded_nonneg g hg hA hB)) (add_nonneg (atom1871Coded_nonneg g hg hA hB) (add_nonneg (atom1872Coded_nonneg g hg hA hB) (atom1873Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1874Coded_nonneg g hg hA hB) (atom1875Coded_nonneg g hg hA hB)) (add_nonneg (atom1876Coded_nonneg g hg hA hB) (add_nonneg (atom1877Coded_nonneg g hg hA hB) (atom1878Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1879Coded_nonneg g hg hA hB) (atom1880Coded_nonneg g hg hA hB)) (add_nonneg (atom1881Coded_nonneg g hg hA hB) (add_nonneg (atom1882Coded_nonneg g hg hA hB) (atom1883Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1884Coded_nonneg g hg hA hB) (atom1885Coded_nonneg g hg hA hB)) (add_nonneg (atom1886Coded_nonneg g hg hA hB) (add_nonneg (atom1887Coded_nonneg g hg hA hB) (atom1888Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
