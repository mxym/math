import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1889 : SparsePolynomial.Poly := [([7,17,23], 1)]
theorem eval_atom1889 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1889 = ((g 7) * (g 17) * (g 23)) := by
  norm_num [atom1889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1889_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (690781818988800 : Int) atom1889) := by
  rw [SparsePolynomial.eval_scale, eval_atom1889]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1889Coded : CoefficientMerge.Poly := [(4463, 1)]
theorem atom1889Coded_decode : atom1889 = SparsePolynomial.decodeCubic 24 atom1889Coded := by decide +kernel
theorem atom1889Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) := by
  have h := atom1889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1890 : SparsePolynomial.Poly := [([7,18,18], 1)]
theorem eval_atom1890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1890 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202067913062400 : Int) atom1890) := by
  rw [SparsePolynomial.eval_scale, eval_atom1890]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1890Coded : CoefficientMerge.Poly := [(4482, 1)]
theorem atom1890Coded_decode : atom1890 = SparsePolynomial.decodeCubic 24 atom1890Coded := by decide +kernel
theorem atom1890Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded) := by
  have h := atom1890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1891 : SparsePolynomial.Poly := [([7,18,19], 1)]
theorem eval_atom1891 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1891 = ((g 7) * (g 18) * (g 19)) := by
  norm_num [atom1891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1891_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390017626521600 : Int) atom1891) := by
  rw [SparsePolynomial.eval_scale, eval_atom1891]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1891Coded : CoefficientMerge.Poly := [(4483, 1)]
theorem atom1891Coded_decode : atom1891 = SparsePolynomial.decodeCubic 24 atom1891Coded := by decide +kernel
theorem atom1891Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) := by
  have h := atom1891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1892 : SparsePolynomial.Poly := [([7,18,20], 1)]
theorem eval_atom1892 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1892 = ((g 7) * (g 18) * (g 20)) := by
  norm_num [atom1892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1892_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (587162124595200 : Int) atom1892) := by
  rw [SparsePolynomial.eval_scale, eval_atom1892]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1892Coded : CoefficientMerge.Poly := [(4484, 1)]
theorem atom1892Coded_decode : atom1892 = SparsePolynomial.decodeCubic 24 atom1892Coded := by decide +kernel
theorem atom1892Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) := by
  have h := atom1892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1893 : SparsePolynomial.Poly := [([7,18,21], 1)]
theorem eval_atom1893 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1893 = ((g 7) * (g 18) * (g 21)) := by
  norm_num [atom1893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1893_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (591060221875200 : Int) atom1893) := by
  rw [SparsePolynomial.eval_scale, eval_atom1893]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1893Coded : CoefficientMerge.Poly := [(4485, 1)]
theorem atom1893Coded_decode : atom1893 = SparsePolynomial.decodeCubic 24 atom1893Coded := by decide +kernel
theorem atom1893Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded) := by
  have h := atom1893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1894 : SparsePolynomial.Poly := [([7,18,22], 1)]
theorem eval_atom1894 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1894 = ((g 7) * (g 18) * (g 22)) := by
  norm_num [atom1894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1894_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (465720930796800 : Int) atom1894) := by
  rw [SparsePolynomial.eval_scale, eval_atom1894]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1894Coded : CoefficientMerge.Poly := [(4486, 1)]
theorem atom1894Coded_decode : atom1894 = SparsePolynomial.decodeCubic 24 atom1894Coded := by decide +kernel
theorem atom1894Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) := by
  have h := atom1894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1895 : SparsePolynomial.Poly := [([7,18,23], 1)]
theorem eval_atom1895 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1895 = ((g 7) * (g 18) * (g 23)) := by
  norm_num [atom1895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1895_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (672974601868800 : Int) atom1895) := by
  rw [SparsePolynomial.eval_scale, eval_atom1895]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1895Coded : CoefficientMerge.Poly := [(4487, 1)]
theorem atom1895Coded_decode : atom1895 = SparsePolynomial.decodeCubic 24 atom1895Coded := by decide +kernel
theorem atom1895Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded) := by
  have h := atom1895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1896 : SparsePolynomial.Poly := [([7,19,19], 1)]
theorem eval_atom1896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1896 = ((g 7) * (g 19) * (g 19)) := by
  norm_num [atom1896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129207041187840 : Int) atom1896) := by
  rw [SparsePolynomial.eval_scale, eval_atom1896]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1896Coded : CoefficientMerge.Poly := [(4507, 1)]
theorem atom1896Coded_decode : atom1896 = SparsePolynomial.decodeCubic 24 atom1896Coded := by decide +kernel
theorem atom1896Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) := by
  have h := atom1896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1897 : SparsePolynomial.Poly := [([7,19,20], 1)]
theorem eval_atom1897 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1897 = ((g 7) * (g 19) * (g 20)) := by
  norm_num [atom1897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1897_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426796764979200 : Int) atom1897) := by
  rw [SparsePolynomial.eval_scale, eval_atom1897]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1897Coded : CoefficientMerge.Poly := [(4508, 1)]
theorem atom1897Coded_decode : atom1897 = SparsePolynomial.decodeCubic 24 atom1897Coded := by decide +kernel
theorem atom1897Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) := by
  have h := atom1897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1898 : SparsePolynomial.Poly := [([7,19,21], 1)]
theorem eval_atom1898 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1898 = ((g 7) * (g 19) * (g 21)) := by
  norm_num [atom1898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1898_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (432844721971200 : Int) atom1898) := by
  rw [SparsePolynomial.eval_scale, eval_atom1898]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1898Coded : CoefficientMerge.Poly := [(4509, 1)]
theorem atom1898Coded_decode : atom1898 = SparsePolynomial.decodeCubic 24 atom1898Coded := by decide +kernel
theorem atom1898Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded) := by
  have h := atom1898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1899 : SparsePolynomial.Poly := [([7,19,22], 1)]
theorem eval_atom1899 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1899 = ((g 7) * (g 19) * (g 22)) := by
  norm_num [atom1899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1899_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (378326949996800 : Int) atom1899) := by
  rw [SparsePolynomial.eval_scale, eval_atom1899]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1899Coded : CoefficientMerge.Poly := [(4510, 1)]
theorem atom1899Coded_decode : atom1899 = SparsePolynomial.decodeCubic 24 atom1899Coded := by decide +kernel
theorem atom1899Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) := by
  have h := atom1899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1900 : SparsePolynomial.Poly := [([7,19,23], 1)]
theorem eval_atom1900 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1900 = ((g 7) * (g 19) * (g 23)) := by
  norm_num [atom1900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1900_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440381097072000 : Int) atom1900) := by
  rw [SparsePolynomial.eval_scale, eval_atom1900]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1900Coded : CoefficientMerge.Poly := [(4511, 1)]
theorem atom1900Coded_decode : atom1900 = SparsePolynomial.decodeCubic 24 atom1900Coded := by decide +kernel
theorem atom1900Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded) := by
  have h := atom1900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1901 : SparsePolynomial.Poly := [([7,20,20], 1)]
theorem eval_atom1901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1901 = ((g 7) * (g 20) * (g 20)) := by
  norm_num [atom1901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309267950745600 : Int) atom1901) := by
  rw [SparsePolynomial.eval_scale, eval_atom1901]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1901Coded : CoefficientMerge.Poly := [(4532, 1)]
theorem atom1901Coded_decode : atom1901 = SparsePolynomial.decodeCubic 24 atom1901Coded := by decide +kernel
theorem atom1901Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) := by
  have h := atom1901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1902 : SparsePolynomial.Poly := [([7,20,21], 1)]
theorem eval_atom1902 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1902 = ((g 7) * (g 20) * (g 21)) := by
  norm_num [atom1902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1902_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450681470131200 : Int) atom1902) := by
  rw [SparsePolynomial.eval_scale, eval_atom1902]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1902Coded : CoefficientMerge.Poly := [(4533, 1)]
theorem atom1902Coded_decode : atom1902 = SparsePolynomial.decodeCubic 24 atom1902Coded := by decide +kernel
theorem atom1902Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) := by
  have h := atom1902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1903 : SparsePolynomial.Poly := [([7,20,22], 1)]
theorem eval_atom1903 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1903 = ((g 7) * (g 20) * (g 22)) := by
  norm_num [atom1903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1903_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (366850113996800 : Int) atom1903) := by
  rw [SparsePolynomial.eval_scale, eval_atom1903]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1903Coded : CoefficientMerge.Poly := [(4534, 1)]
theorem atom1903Coded_decode : atom1903 = SparsePolynomial.decodeCubic 24 atom1903Coded := by decide +kernel
theorem atom1903Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded) := by
  have h := atom1903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1904 : SparsePolynomial.Poly := [([7,20,23], 1)]
theorem eval_atom1904 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1904 = ((g 7) * (g 20) * (g 23)) := by
  norm_num [atom1904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1904_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (455881349347200 : Int) atom1904) := by
  rw [SparsePolynomial.eval_scale, eval_atom1904]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1904Coded : CoefficientMerge.Poly := [(4535, 1)]
theorem atom1904Coded_decode : atom1904 = SparsePolynomial.decodeCubic 24 atom1904Coded := by decide +kernel
theorem atom1904Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) := by
  have h := atom1904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1905 : SparsePolynomial.Poly := [([7,21,21], 1)]
theorem eval_atom1905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1905 = ((g 7) * (g 21) * (g 21)) := by
  norm_num [atom1905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89500313548800 : Int) atom1905) := by
  rw [SparsePolynomial.eval_scale, eval_atom1905]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1905Coded : CoefficientMerge.Poly := [(4557, 1)]
theorem atom1905Coded_decode : atom1905 = SparsePolynomial.decodeCubic 24 atom1905Coded := by decide +kernel
theorem atom1905Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded) := by
  have h := atom1905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1906 : SparsePolynomial.Poly := [([7,21,22], 1)]
theorem eval_atom1906 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1906 = ((g 7) * (g 21) * (g 22)) := by
  norm_num [atom1906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1906_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153592979366400 : Int) atom1906) := by
  rw [SparsePolynomial.eval_scale, eval_atom1906]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1906Coded : CoefficientMerge.Poly := [(4558, 1)]
theorem atom1906Coded_decode : atom1906 = SparsePolynomial.decodeCubic 24 atom1906Coded := by decide +kernel
theorem atom1906Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) := by
  have h := atom1906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1907 : SparsePolynomial.Poly := [([7,21,23], 1)]
theorem eval_atom1907 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1907 = ((g 7) * (g 21) * (g 23)) := by
  norm_num [atom1907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1907_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (236387787048000 : Int) atom1907) := by
  rw [SparsePolynomial.eval_scale, eval_atom1907]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1907Coded : CoefficientMerge.Poly := [(4559, 1)]
theorem atom1907Coded_decode : atom1907 = SparsePolynomial.decodeCubic 24 atom1907Coded := by decide +kernel
theorem atom1907Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) := by
  have h := atom1907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1908 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom1908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1908 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15968023948800 : Int) atom1908) := by
  rw [SparsePolynomial.eval_scale, eval_atom1908]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1908Coded : CoefficientMerge.Poly := [(4808, 1)]
theorem atom1908Coded_decode : atom1908 = SparsePolynomial.decodeCubic 24 atom1908Coded := by decide +kernel
theorem atom1908Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded) := by
  have h := atom1908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1909 : SparsePolynomial.Poly := [([8,8,9], 1)]
theorem eval_atom1909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1909 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30188327122800 : Int) atom1909) := by
  rw [SparsePolynomial.eval_scale, eval_atom1909]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1909Coded : CoefficientMerge.Poly := [(4809, 1)]
theorem atom1909Coded_decode : atom1909 = SparsePolynomial.decodeCubic 24 atom1909Coded := by decide +kernel
theorem atom1909Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) := by
  have h := atom1909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1910 : SparsePolynomial.Poly := [([8,8,10], 1)]
theorem eval_atom1910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1910 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2502889795296 : Int) atom1910) := by
  rw [SparsePolynomial.eval_scale, eval_atom1910]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1910Coded : CoefficientMerge.Poly := [(4810, 1)]
theorem atom1910Coded_decode : atom1910 = SparsePolynomial.decodeCubic 24 atom1910Coded := by decide +kernel
theorem atom1910Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded) := by
  have h := atom1910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1911 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom1911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1911 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1911) := by
  rw [SparsePolynomial.eval_scale, eval_atom1911]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1911Coded : CoefficientMerge.Poly := [(4811, 1)]
theorem atom1911Coded_decode : atom1911 = SparsePolynomial.decodeCubic 24 atom1911Coded := by decide +kernel
theorem atom1911Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) := by
  have h := atom1911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1912 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom1912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1912 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35074459173600 : Int) atom1912) := by
  rw [SparsePolynomial.eval_scale, eval_atom1912]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1912Coded : CoefficientMerge.Poly := [(4833, 1)]
theorem atom1912Coded_decode : atom1912 = SparsePolynomial.decodeCubic 24 atom1912Coded := by decide +kernel
theorem atom1912Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) := by
  have h := atom1912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1913 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom1913 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1913 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom1913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1913_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17799156411696 : Int) atom1913) := by
  rw [SparsePolynomial.eval_scale, eval_atom1913]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1913Coded : CoefficientMerge.Poly := [(4834, 1)]
theorem atom1913Coded_decode : atom1913 = SparsePolynomial.decodeCubic 24 atom1913Coded := by decide +kernel
theorem atom1913Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded) := by
  have h := atom1913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1914 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom1914 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1914 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom1914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1914_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1914) := by
  rw [SparsePolynomial.eval_scale, eval_atom1914]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1914Coded : CoefficientMerge.Poly := [(4838, 1)]
theorem atom1914Coded_decode : atom1914 = SparsePolynomial.decodeCubic 24 atom1914Coded := by decide +kernel
theorem atom1914Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) := by
  have h := atom1914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1915 : SparsePolynomial.Poly := [([8,9,15], 1)]
theorem eval_atom1915 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1915 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom1915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1915_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom1915) := by
  rw [SparsePolynomial.eval_scale, eval_atom1915]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1915Coded : CoefficientMerge.Poly := [(4839, 1)]
theorem atom1915Coded_decode : atom1915 = SparsePolynomial.decodeCubic 24 atom1915Coded := by decide +kernel
theorem atom1915Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded) := by
  have h := atom1915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1916 : SparsePolynomial.Poly := [([8,9,16], 1)]
theorem eval_atom1916 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1916 = ((g 8) * (g 9) * (g 16)) := by
  norm_num [atom1916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1916_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom1916) := by
  rw [SparsePolynomial.eval_scale, eval_atom1916]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1916Coded : CoefficientMerge.Poly := [(4840, 1)]
theorem atom1916Coded_decode : atom1916 = SparsePolynomial.decodeCubic 24 atom1916Coded := by decide +kernel
theorem atom1916Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) := by
  have h := atom1916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1917 : SparsePolynomial.Poly := [([8,9,17], 1)]
theorem eval_atom1917 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1917 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom1917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1917_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom1917) := by
  rw [SparsePolynomial.eval_scale, eval_atom1917]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1917Coded : CoefficientMerge.Poly := [(4841, 1)]
theorem atom1917Coded_decode : atom1917 = SparsePolynomial.decodeCubic 24 atom1917Coded := by decide +kernel
theorem atom1917Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) := by
  have h := atom1917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1918 : SparsePolynomial.Poly := [([8,9,19], 1)]
theorem eval_atom1918 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1918 = ((g 8) * (g 9) * (g 19)) := by
  norm_num [atom1918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1918_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1197778982400 : Int) atom1918) := by
  rw [SparsePolynomial.eval_scale, eval_atom1918]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1918Coded : CoefficientMerge.Poly := [(4843, 1)]
theorem atom1918Coded_decode : atom1918 = SparsePolynomial.decodeCubic 24 atom1918Coded := by decide +kernel
theorem atom1918Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded) := by
  have h := atom1918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1919 : SparsePolynomial.Poly := [([8,9,21], 1)]
theorem eval_atom1919 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1919 = ((g 8) * (g 9) * (g 21)) := by
  norm_num [atom1919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1919_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45125791603200 : Int) atom1919) := by
  rw [SparsePolynomial.eval_scale, eval_atom1919]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1919Coded : CoefficientMerge.Poly := [(4845, 1)]
theorem atom1919Coded_decode : atom1919 = SparsePolynomial.decodeCubic 24 atom1919Coded := by decide +kernel
theorem atom1919Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) := by
  have h := atom1919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1920 : SparsePolynomial.Poly := [([8,9,22], 1)]
theorem eval_atom1920 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1920 = ((g 8) * (g 9) * (g 22)) := by
  norm_num [atom1920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1920_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87856025241600 : Int) atom1920) := by
  rw [SparsePolynomial.eval_scale, eval_atom1920]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1920Coded : CoefficientMerge.Poly := [(4846, 1)]
theorem atom1920Coded_decode : atom1920 = SparsePolynomial.decodeCubic 24 atom1920Coded := by decide +kernel
theorem atom1920Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded) := by
  have h := atom1920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1921 : SparsePolynomial.Poly := [([8,9,23], 1)]
theorem eval_atom1921 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1921 = ((g 8) * (g 9) * (g 23)) := by
  norm_num [atom1921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1921_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137822544921600 : Int) atom1921) := by
  rw [SparsePolynomial.eval_scale, eval_atom1921]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1921Coded : CoefficientMerge.Poly := [(4847, 1)]
theorem atom1921Coded_decode : atom1921 = SparsePolynomial.decodeCubic 24 atom1921Coded := by decide +kernel
theorem atom1921Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) := by
  have h := atom1921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1922 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom1922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1922 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5326574012496 : Int) atom1922) := by
  rw [SparsePolynomial.eval_scale, eval_atom1922]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1922Coded : CoefficientMerge.Poly := [(4858, 1)]
theorem atom1922Coded_decode : atom1922 = SparsePolynomial.decodeCubic 24 atom1922Coded := by decide +kernel
theorem atom1922Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) := by
  have h := atom1922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1923 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom1923 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1923 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom1923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1923_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2124375690096 : Int) atom1923) := by
  rw [SparsePolynomial.eval_scale, eval_atom1923]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1923Coded : CoefficientMerge.Poly := [(4859, 1)]
theorem atom1923Coded_decode : atom1923 = SparsePolynomial.decodeCubic 24 atom1923Coded := by decide +kernel
theorem atom1923Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded) := by
  have h := atom1923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1924 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom1924 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1924 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom1924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1924_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1103782947696 : Int) atom1924) := by
  rw [SparsePolynomial.eval_scale, eval_atom1924]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1924Coded : CoefficientMerge.Poly := [(4860, 1)]
theorem atom1924Coded_decode : atom1924 = SparsePolynomial.decodeCubic 24 atom1924Coded := by decide +kernel
theorem atom1924Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) := by
  have h := atom1924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1925 : SparsePolynomial.Poly := [([8,10,13], 1)]
theorem eval_atom1925 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1925 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom1925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1925_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6249271357296 : Int) atom1925) := by
  rw [SparsePolynomial.eval_scale, eval_atom1925]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1925Coded : CoefficientMerge.Poly := [(4861, 1)]
theorem atom1925Coded_decode : atom1925 = SparsePolynomial.decodeCubic 24 atom1925Coded := by decide +kernel
theorem atom1925Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded) := by
  have h := atom1925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1926 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom1926 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1926 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom1926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1926_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11394759766896 : Int) atom1926) := by
  rw [SparsePolynomial.eval_scale, eval_atom1926]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1926Coded : CoefficientMerge.Poly := [(4862, 1)]
theorem atom1926Coded_decode : atom1926 = SparsePolynomial.decodeCubic 24 atom1926Coded := by decide +kernel
theorem atom1926Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) := by
  have h := atom1926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1927 : SparsePolynomial.Poly := [([8,10,15], 1)]
theorem eval_atom1927 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1927 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom1927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1927_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16540248176496 : Int) atom1927) := by
  rw [SparsePolynomial.eval_scale, eval_atom1927]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1927Coded : CoefficientMerge.Poly := [(4863, 1)]
theorem atom1927Coded_decode : atom1927 = SparsePolynomial.decodeCubic 24 atom1927Coded := by decide +kernel
theorem atom1927Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) := by
  have h := atom1927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1928 : SparsePolynomial.Poly := [([8,10,16], 1)]
theorem eval_atom1928 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1928 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom1928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1928_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21685736586096 : Int) atom1928) := by
  rw [SparsePolynomial.eval_scale, eval_atom1928]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1928Coded : CoefficientMerge.Poly := [(4864, 1)]
theorem atom1928Coded_decode : atom1928 = SparsePolynomial.decodeCubic 24 atom1928Coded := by decide +kernel
theorem atom1928Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded) := by
  have h := atom1928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1929 : SparsePolynomial.Poly := [([8,10,17], 1)]
theorem eval_atom1929 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1929 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom1929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1929_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26831224995696 : Int) atom1929) := by
  rw [SparsePolynomial.eval_scale, eval_atom1929]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1929Coded : CoefficientMerge.Poly := [(4865, 1)]
theorem atom1929Coded_decode : atom1929 = SparsePolynomial.decodeCubic 24 atom1929Coded := by decide +kernel
theorem atom1929Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) := by
  have h := atom1929_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1929Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1930 : SparsePolynomial.Poly := [([8,10,18], 1)]
theorem eval_atom1930 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1930 = ((g 8) * (g 10) * (g 18)) := by
  norm_num [atom1930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1930_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249966120888 : Int) atom1930) := by
  rw [SparsePolynomial.eval_scale, eval_atom1930]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1930Coded : CoefficientMerge.Poly := [(4866, 1)]
theorem atom1930Coded_decode : atom1930 = SparsePolynomial.decodeCubic 24 atom1930Coded := by decide +kernel
theorem atom1930Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded) := by
  have h := atom1930_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1930Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1931 : SparsePolynomial.Poly := [([8,10,21], 1)]
theorem eval_atom1931 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1931 = ((g 8) * (g 10) * (g 21)) := by
  norm_num [atom1931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1931_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81191673285228 : Int) atom1931) := by
  rw [SparsePolynomial.eval_scale, eval_atom1931]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1931Coded : CoefficientMerge.Poly := [(4869, 1)]
theorem atom1931Coded_decode : atom1931 = SparsePolynomial.decodeCubic 24 atom1931Coded := by decide +kernel
theorem atom1931Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) := by
  have h := atom1931_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1931Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1932 : SparsePolynomial.Poly := [([8,10,22], 1)]
theorem eval_atom1932 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1932 = ((g 8) * (g 10) * (g 22)) := by
  norm_num [atom1932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1932_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162633312691344 : Int) atom1932) := by
  rw [SparsePolynomial.eval_scale, eval_atom1932]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1932Coded : CoefficientMerge.Poly := [(4870, 1)]
theorem atom1932Coded_decode : atom1932 = SparsePolynomial.decodeCubic 24 atom1932Coded := by decide +kernel
theorem atom1932Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) := by
  have h := atom1932_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1932Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1933 : SparsePolynomial.Poly := [([8,10,23], 1)]
theorem eval_atom1933 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1933 = ((g 8) * (g 10) * (g 23)) := by
  norm_num [atom1933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1933_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (258589462107042 : Int) atom1933) := by
  rw [SparsePolynomial.eval_scale, eval_atom1933]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1933Coded : CoefficientMerge.Poly := [(4871, 1)]
theorem atom1933Coded_decode : atom1933 = SparsePolynomial.decodeCubic 24 atom1933Coded := by decide +kernel
theorem atom1933Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded) := by
  have h := atom1933_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1933Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1934 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom1934 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1934 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1934_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25565759604000 : Int) atom1934) := by
  rw [SparsePolynomial.eval_scale, eval_atom1934]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1934Coded : CoefficientMerge.Poly := [(4883, 1)]
theorem atom1934Coded_decode : atom1934 = SparsePolynomial.decodeCubic 24 atom1934Coded := by decide +kernel
theorem atom1934Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) := by
  have h := atom1934_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1934Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1935 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom1935 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1935 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom1935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1935_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31374810482400 : Int) atom1935) := by
  rw [SparsePolynomial.eval_scale, eval_atom1935]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1935Coded : CoefficientMerge.Poly := [(4884, 1)]
theorem atom1935Coded_decode : atom1935 = SparsePolynomial.decodeCubic 24 atom1935Coded := by decide +kernel
theorem atom1935Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded) := by
  have h := atom1935_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1935Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1936 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom1936 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1936 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom1936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1936_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34479113407200 : Int) atom1936) := by
  rw [SparsePolynomial.eval_scale, eval_atom1936]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1936Coded : CoefficientMerge.Poly := [(4885, 1)]
theorem atom1936Coded_decode : atom1936 = SparsePolynomial.decodeCubic 24 atom1936Coded := by decide +kernel
theorem atom1936Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) := by
  have h := atom1936_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1936Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1937 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom1937 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1937 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom1937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1937_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37583416332000 : Int) atom1937) := by
  rw [SparsePolynomial.eval_scale, eval_atom1937]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1937Coded : CoefficientMerge.Poly := [(4886, 1)]
theorem atom1937Coded_decode : atom1937 = SparsePolynomial.decodeCubic 24 atom1937Coded := by decide +kernel
theorem atom1937Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) := by
  have h := atom1937_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1937Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1938 : SparsePolynomial.Poly := [([8,11,15], 1)]
theorem eval_atom1938 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1938 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom1938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1938_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40687719256800 : Int) atom1938) := by
  rw [SparsePolynomial.eval_scale, eval_atom1938]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1938Coded : CoefficientMerge.Poly := [(4887, 1)]
theorem atom1938Coded_decode : atom1938 = SparsePolynomial.decodeCubic 24 atom1938Coded := by decide +kernel
theorem atom1938Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded) := by
  have h := atom1938_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1938Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1939 : SparsePolynomial.Poly := [([8,11,16], 1)]
theorem eval_atom1939 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1939 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom1939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1939_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46875062757600 : Int) atom1939) := by
  rw [SparsePolynomial.eval_scale, eval_atom1939]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1939Coded : CoefficientMerge.Poly := [(4888, 1)]
theorem atom1939Coded_decode : atom1939 = SparsePolynomial.decodeCubic 24 atom1939Coded := by decide +kernel
theorem atom1939Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) := by
  have h := atom1939_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1939Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1940 : SparsePolynomial.Poly := [([8,11,17], 1)]
theorem eval_atom1940 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1940 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom1940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1940_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53062406258400 : Int) atom1940) := by
  rw [SparsePolynomial.eval_scale, eval_atom1940]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1940Coded : CoefficientMerge.Poly := [(4889, 1)]
theorem atom1940Coded_decode : atom1940 = SparsePolynomial.decodeCubic 24 atom1940Coded := by decide +kernel
theorem atom1940Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded) := by
  have h := atom1940_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1940Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1941 : SparsePolynomial.Poly := [([8,11,18], 1)]
theorem eval_atom1941 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1941 = ((g 8) * (g 11) * (g 18)) := by
  norm_num [atom1941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1941_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43596916084656 : Int) atom1941) := by
  rw [SparsePolynomial.eval_scale, eval_atom1941]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1941Coded : CoefficientMerge.Poly := [(4890, 1)]
theorem atom1941Coded_decode : atom1941 = SparsePolynomial.decodeCubic 24 atom1941Coded := by decide +kernel
theorem atom1941Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) := by
  have h := atom1941_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1941Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1942 : SparsePolynomial.Poly := [([8,11,19], 1)]
theorem eval_atom1942 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1942 = ((g 8) * (g 11) * (g 19)) := by
  norm_num [atom1942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1942_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40466097239040 : Int) atom1942) := by
  rw [SparsePolynomial.eval_scale, eval_atom1942]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1942Coded : CoefficientMerge.Poly := [(4891, 1)]
theorem atom1942Coded_decode : atom1942 = SparsePolynomial.decodeCubic 24 atom1942Coded := by decide +kernel
theorem atom1942Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) := by
  have h := atom1942_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1942Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1943 : SparsePolynomial.Poly := [([8,11,20], 1)]
theorem eval_atom1943 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1943 = ((g 8) * (g 11) * (g 20)) := by
  norm_num [atom1943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1943_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59252072164560 : Int) atom1943) := by
  rw [SparsePolynomial.eval_scale, eval_atom1943]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1943Coded : CoefficientMerge.Poly := [(4892, 1)]
theorem atom1943Coded_decode : atom1943 = SparsePolynomial.decodeCubic 24 atom1943Coded := by decide +kernel
theorem atom1943Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded) := by
  have h := atom1943_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1943Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1944 : SparsePolynomial.Poly := [([8,11,21], 1)]
theorem eval_atom1944 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1944 = ((g 8) * (g 11) * (g 21)) := by
  norm_num [atom1944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1944_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145083165594840 : Int) atom1944) := by
  rw [SparsePolynomial.eval_scale, eval_atom1944]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1944Coded : CoefficientMerge.Poly := [(4893, 1)]
theorem atom1944Coded_decode : atom1944 = SparsePolynomial.decodeCubic 24 atom1944Coded := by decide +kernel
theorem atom1944Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) := by
  have h := atom1944_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1944Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1945 : SparsePolynomial.Poly := [([8,11,22], 1)]
theorem eval_atom1945 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1945 = ((g 8) * (g 11) * (g 22)) := by
  norm_num [atom1945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1945_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241202304677664 : Int) atom1945) := by
  rw [SparsePolynomial.eval_scale, eval_atom1945]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1945Coded : CoefficientMerge.Poly := [(4894, 1)]
theorem atom1945Coded_decode : atom1945 = SparsePolynomial.decodeCubic 24 atom1945Coded := by decide +kernel
theorem atom1945Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded) := by
  have h := atom1945_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1945Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1946 : SparsePolynomial.Poly := [([8,11,23], 1)]
theorem eval_atom1946 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1946 = ((g 8) * (g 11) * (g 23)) := by
  norm_num [atom1946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1946_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351539881100100 : Int) atom1946) := by
  rw [SparsePolynomial.eval_scale, eval_atom1946]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1946Coded : CoefficientMerge.Poly := [(4895, 1)]
theorem atom1946Coded_decode : atom1946 = SparsePolynomial.decodeCubic 24 atom1946Coded := by decide +kernel
theorem atom1946Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) := by
  have h := atom1946_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1946Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1947 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom1947 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1947 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1947_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34577008804800 : Int) atom1947) := by
  rw [SparsePolynomial.eval_scale, eval_atom1947]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1947Coded : CoefficientMerge.Poly := [(4908, 1)]
theorem atom1947Coded_decode : atom1947 = SparsePolynomial.decodeCubic 24 atom1947Coded := by decide +kernel
theorem atom1947Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) := by
  have h := atom1947_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1947Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1948 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom1948 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1948 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom1948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1948_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63548730907200 : Int) atom1948) := by
  rw [SparsePolynomial.eval_scale, eval_atom1948]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1948Coded : CoefficientMerge.Poly := [(4909, 1)]
theorem atom1948Coded_decode : atom1948 = SparsePolynomial.decodeCubic 24 atom1948Coded := by decide +kernel
theorem atom1948Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded) := by
  have h := atom1948_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1948Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1949 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom1949 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1949 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom1949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1949_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69757336756800 : Int) atom1949) := by
  rw [SparsePolynomial.eval_scale, eval_atom1949]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1949Coded : CoefficientMerge.Poly := [(4910, 1)]
theorem atom1949Coded_decode : atom1949 = SparsePolynomial.decodeCubic 24 atom1949Coded := by decide +kernel
theorem atom1949Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) := by
  have h := atom1949_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1949Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1950 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom1950 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1950 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom1950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1950_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75965942606400 : Int) atom1950) := by
  rw [SparsePolynomial.eval_scale, eval_atom1950]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1950Coded : CoefficientMerge.Poly := [(4911, 1)]
theorem atom1950Coded_decode : atom1950 = SparsePolynomial.decodeCubic 24 atom1950Coded := by decide +kernel
theorem atom1950Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded) := by
  have h := atom1950_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1950Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1951 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom1951 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1951 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom1951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1951_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82174548456000 : Int) atom1951) := by
  rw [SparsePolynomial.eval_scale, eval_atom1951]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1951Coded : CoefficientMerge.Poly := [(4912, 1)]
theorem atom1951Coded_decode : atom1951 = SparsePolynomial.decodeCubic 24 atom1951Coded := by decide +kernel
theorem atom1951Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) := by
  have h := atom1951_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1951Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1952 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom1952 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1952 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom1952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1952_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88383154305600 : Int) atom1952) := by
  rw [SparsePolynomial.eval_scale, eval_atom1952]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1952Coded : CoefficientMerge.Poly := [(4913, 1)]
theorem atom1952Coded_decode : atom1952 = SparsePolynomial.decodeCubic 24 atom1952Coded := by decide +kernel
theorem atom1952Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) := by
  have h := atom1952_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1952Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1953 : SparsePolynomial.Poly := [([8,12,18], 1)]
theorem eval_atom1953 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1953 = ((g 8) * (g 12) * (g 18)) := by
  norm_num [atom1953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1953_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124602611211936 : Int) atom1953) := by
  rw [SparsePolynomial.eval_scale, eval_atom1953]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1953Coded : CoefficientMerge.Poly := [(4914, 1)]
theorem atom1953Coded_decode : atom1953 = SparsePolynomial.decodeCubic 24 atom1953Coded := by decide +kernel
theorem atom1953Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded) := by
  have h := atom1953_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1953Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1954 : SparsePolynomial.Poly := [([8,12,19], 1)]
theorem eval_atom1954 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1954 = ((g 8) * (g 12) * (g 19)) := by
  norm_num [atom1954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1954_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106592002007040 : Int) atom1954) := by
  rw [SparsePolynomial.eval_scale, eval_atom1954]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1954Coded : CoefficientMerge.Poly := [(4915, 1)]
theorem atom1954Coded_decode : atom1954 = SparsePolynomial.decodeCubic 24 atom1954Coded := by decide +kernel
theorem atom1954Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) := by
  have h := atom1954_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1954Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1955 : SparsePolynomial.Poly := [([8,12,20], 1)]
theorem eval_atom1955 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1955 = ((g 8) * (g 12) * (g 20)) := by
  norm_num [atom1955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1955_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198627432996960 : Int) atom1955) := by
  rw [SparsePolynomial.eval_scale, eval_atom1955]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1955Coded : CoefficientMerge.Poly := [(4916, 1)]
theorem atom1955Coded_decode : atom1955 = SparsePolynomial.decodeCubic 24 atom1955Coded := by decide +kernel
theorem atom1955Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded) := by
  have h := atom1955_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1955Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1956 : SparsePolynomial.Poly := [([8,12,21], 1)]
theorem eval_atom1956 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1956 = ((g 8) * (g 12) * (g 21)) := by
  norm_num [atom1956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1956_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222778113679440 : Int) atom1956) := by
  rw [SparsePolynomial.eval_scale, eval_atom1956]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1956Coded : CoefficientMerge.Poly := [(4917, 1)]
theorem atom1956Coded_decode : atom1956 = SparsePolynomial.decodeCubic 24 atom1956Coded := by decide +kernel
theorem atom1956Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) := by
  have h := atom1956_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1956Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1957 : SparsePolynomial.Poly := [([8,12,22], 1)]
theorem eval_atom1957 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1957 = ((g 8) * (g 12) * (g 22)) := by
  norm_num [atom1957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1957_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316603111771584 : Int) atom1957) := by
  rw [SparsePolynomial.eval_scale, eval_atom1957]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1957Coded : CoefficientMerge.Poly := [(4918, 1)]
theorem atom1957Coded_decode : atom1957 = SparsePolynomial.decodeCubic 24 atom1957Coded := by decide +kernel
theorem atom1957Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) := by
  have h := atom1957_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1957Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1958 : SparsePolynomial.Poly := [([8,12,23], 1)]
theorem eval_atom1958 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1958 = ((g 8) * (g 12) * (g 23)) := by
  norm_num [atom1958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1958_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419646672660600 : Int) atom1958) := by
  rw [SparsePolynomial.eval_scale, eval_atom1958]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1958Coded : CoefficientMerge.Poly := [(4919, 1)]
theorem atom1958Coded_decode : atom1958 = SparsePolynomial.decodeCubic 24 atom1958Coded := by decide +kernel
theorem atom1958Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded) := by
  have h := atom1958_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1958Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1959 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom1959 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1959 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1959_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57739680028800 : Int) atom1959) := by
  rw [SparsePolynomial.eval_scale, eval_atom1959]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1959Coded : CoefficientMerge.Poly := [(4933, 1)]
theorem atom1959Coded_decode : atom1959 = SparsePolynomial.decodeCubic 24 atom1959Coded := by decide +kernel
theorem atom1959Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) := by
  have h := atom1959_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1959Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1960 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom1960 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1960 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom1960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1960_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108361788796800 : Int) atom1960) := by
  rw [SparsePolynomial.eval_scale, eval_atom1960]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1960Coded : CoefficientMerge.Poly := [(4934, 1)]
theorem atom1960Coded_decode : atom1960 = SparsePolynomial.decodeCubic 24 atom1960Coded := by decide +kernel
theorem atom1960Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded) := by
  have h := atom1960_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1960Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1961 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom1961 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1961 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom1961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1961_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110488023676800 : Int) atom1961) := by
  rw [SparsePolynomial.eval_scale, eval_atom1961]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1961Coded : CoefficientMerge.Poly := [(4935, 1)]
theorem atom1961Coded_decode : atom1961 = SparsePolynomial.decodeCubic 24 atom1961Coded := by decide +kernel
theorem atom1961Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) := by
  have h := atom1961_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1961Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1962 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom1962 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1962 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom1962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1962_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115697299132800 : Int) atom1962) := by
  rw [SparsePolynomial.eval_scale, eval_atom1962]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1962Coded : CoefficientMerge.Poly := [(4936, 1)]
theorem atom1962Coded_decode : atom1962 = SparsePolynomial.decodeCubic 24 atom1962Coded := by decide +kernel
theorem atom1962Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) := by
  have h := atom1962_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1962Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1963 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom1963 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1963 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom1963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1963_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120906574588800 : Int) atom1963) := by
  rw [SparsePolynomial.eval_scale, eval_atom1963]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1963Coded : CoefficientMerge.Poly := [(4937, 1)]
theorem atom1963Coded_decode : atom1963 = SparsePolynomial.decodeCubic 24 atom1963Coded := by decide +kernel
theorem atom1963Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded) := by
  have h := atom1963_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1963Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1964 : SparsePolynomial.Poly := [([8,13,18], 1)]
theorem eval_atom1964 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1964 = ((g 8) * (g 13) * (g 18)) := by
  norm_num [atom1964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1964_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152275157496000 : Int) atom1964) := by
  rw [SparsePolynomial.eval_scale, eval_atom1964]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1964Coded : CoefficientMerge.Poly := [(4938, 1)]
theorem atom1964Coded_decode : atom1964 = SparsePolynomial.decodeCubic 24 atom1964Coded := by decide +kernel
theorem atom1964Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) := by
  have h := atom1964_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1964Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1965 : SparsePolynomial.Poly := [([8,13,19], 1)]
theorem eval_atom1965 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1965 = ((g 8) * (g 13) * (g 19)) := by
  norm_num [atom1965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1965_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142638050016000 : Int) atom1965) := by
  rw [SparsePolynomial.eval_scale, eval_atom1965]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1965Coded : CoefficientMerge.Poly := [(4939, 1)]
theorem atom1965Coded_decode : atom1965 = SparsePolynomial.decodeCubic 24 atom1965Coded := by decide +kernel
theorem atom1965Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded) := by
  have h := atom1965_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1965Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1966 : SparsePolynomial.Poly := [([8,13,20], 1)]
theorem eval_atom1966 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1966 = ((g 8) * (g 13) * (g 20)) := by
  norm_num [atom1966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1966_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245003491656000 : Int) atom1966) := by
  rw [SparsePolynomial.eval_scale, eval_atom1966]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1966Coded : CoefficientMerge.Poly := [(4940, 1)]
theorem atom1966Coded_decode : atom1966 = SparsePolynomial.decodeCubic 24 atom1966Coded := by decide +kernel
theorem atom1966Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) := by
  have h := atom1966_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1966Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1967 : SparsePolynomial.Poly := [([8,13,21], 1)]
theorem eval_atom1967 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1967 = ((g 8) * (g 13) * (g 21)) := by
  norm_num [atom1967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1967_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (267452024162400 : Int) atom1967) := by
  rw [SparsePolynomial.eval_scale, eval_atom1967]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1967Coded : CoefficientMerge.Poly := [(4941, 1)]
theorem atom1967Coded_decode : atom1967 = SparsePolynomial.decodeCubic 24 atom1967Coded := by decide +kernel
theorem atom1967Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) := by
  have h := atom1967_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1967Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1968 : SparsePolynomial.Poly := [([8,13,22], 1)]
theorem eval_atom1968 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1968 = ((g 8) * (g 13) * (g 22)) := by
  norm_num [atom1968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1968_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (367278829948800 : Int) atom1968) := by
  rw [SparsePolynomial.eval_scale, eval_atom1968]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1968Coded : CoefficientMerge.Poly := [(4942, 1)]
theorem atom1968Coded_decode : atom1968 = SparsePolynomial.decodeCubic 24 atom1968Coded := by decide +kernel
theorem atom1968Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded) := by
  have h := atom1968_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1968Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block026 : CoefficientMerge.Poly := [(4463, 690781818988800), (4482, 202067913062400), (4483, 390017626521600), (4484, 587162124595200), (4485, 591060221875200), (4486, 465720930796800), (4487, 672974601868800), (4507, 129207041187840), (4508, 426796764979200), (4509, 432844721971200), (4510, 378326949996800), (4511, 440381097072000), (4532, 309267950745600), (4533, 450681470131200), (4534, 366850113996800), (4535, 455881349347200), (4557, 89500313548800), (4558, 153592979366400), (4559, 236387787048000), (4808, 15968023948800), (4809, 30188327122800), (4810, 2502889795296), (4811, 3083040576000), (4833, 35074459173600), (4834, 17799156411696), (4838, 3083040576000), (4839, 6166081152000), (4840, 9249121728000), (4841, 12332162304000), (4843, 1197778982400), (4845, 45125791603200), (4846, 87856025241600), (4847, 137822544921600), (4858, 5326574012496), (4859, 2124375690096), (4860, 1103782947696), (4861, 6249271357296), (4862, 11394759766896), (4863, 16540248176496), (4864, 21685736586096), (4865, 26831224995696), (4866, 249966120888), (4869, 81191673285228), (4870, 162633312691344), (4871, 258589462107042), (4883, 25565759604000), (4884, 31374810482400), (4885, 34479113407200), (4886, 37583416332000), (4887, 40687719256800), (4888, 46875062757600), (4889, 53062406258400), (4890, 43596916084656), (4891, 40466097239040), (4892, 59252072164560), (4893, 145083165594840), (4894, 241202304677664), (4895, 351539881100100), (4908, 34577008804800), (4909, 63548730907200), (4910, 69757336756800), (4911, 75965942606400), (4912, 82174548456000), (4913, 88383154305600), (4914, 124602611211936), (4915, 106592002007040), (4916, 198627432996960), (4917, 222778113679440), (4918, 316603111771584), (4919, 419646672660600), (4933, 57739680028800), (4934, 108361788796800), (4935, 110488023676800), (4936, 115697299132800), (4937, 120906574588800), (4938, 152275157496000), (4939, 142638050016000), (4940, 245003491656000), (4941, 267452024162400), (4942, 367278829948800)]
theorem block026_data : block026 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)))))))) := by decide +kernel
theorem block026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block026 := by
  rw [block026_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1889Coded_nonneg g hg hA hB) (atom1890Coded_nonneg g hg hA hB)) (add_nonneg (atom1891Coded_nonneg g hg hA hB) (add_nonneg (atom1892Coded_nonneg g hg hA hB) (atom1893Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1894Coded_nonneg g hg hA hB) (atom1895Coded_nonneg g hg hA hB)) (add_nonneg (atom1896Coded_nonneg g hg hA hB) (add_nonneg (atom1897Coded_nonneg g hg hA hB) (atom1898Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1899Coded_nonneg g hg hA hB) (atom1900Coded_nonneg g hg hA hB)) (add_nonneg (atom1901Coded_nonneg g hg hA hB) (add_nonneg (atom1902Coded_nonneg g hg hA hB) (atom1903Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1904Coded_nonneg g hg hA hB) (atom1905Coded_nonneg g hg hA hB)) (add_nonneg (atom1906Coded_nonneg g hg hA hB) (add_nonneg (atom1907Coded_nonneg g hg hA hB) (atom1908Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1909Coded_nonneg g hg hA hB) (atom1910Coded_nonneg g hg hA hB)) (add_nonneg (atom1911Coded_nonneg g hg hA hB) (add_nonneg (atom1912Coded_nonneg g hg hA hB) (atom1913Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1914Coded_nonneg g hg hA hB) (atom1915Coded_nonneg g hg hA hB)) (add_nonneg (atom1916Coded_nonneg g hg hA hB) (add_nonneg (atom1917Coded_nonneg g hg hA hB) (atom1918Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1919Coded_nonneg g hg hA hB) (atom1920Coded_nonneg g hg hA hB)) (add_nonneg (atom1921Coded_nonneg g hg hA hB) (add_nonneg (atom1922Coded_nonneg g hg hA hB) (atom1923Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1924Coded_nonneg g hg hA hB) (atom1925Coded_nonneg g hg hA hB)) (add_nonneg (atom1926Coded_nonneg g hg hA hB) (add_nonneg (atom1927Coded_nonneg g hg hA hB) (atom1928Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1929Coded_nonneg g hg hA hB) (atom1930Coded_nonneg g hg hA hB)) (add_nonneg (atom1931Coded_nonneg g hg hA hB) (add_nonneg (atom1932Coded_nonneg g hg hA hB) (atom1933Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1934Coded_nonneg g hg hA hB) (atom1935Coded_nonneg g hg hA hB)) (add_nonneg (atom1936Coded_nonneg g hg hA hB) (add_nonneg (atom1937Coded_nonneg g hg hA hB) (atom1938Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1939Coded_nonneg g hg hA hB) (atom1940Coded_nonneg g hg hA hB)) (add_nonneg (atom1941Coded_nonneg g hg hA hB) (add_nonneg (atom1942Coded_nonneg g hg hA hB) (atom1943Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1944Coded_nonneg g hg hA hB) (atom1945Coded_nonneg g hg hA hB)) (add_nonneg (atom1946Coded_nonneg g hg hA hB) (add_nonneg (atom1947Coded_nonneg g hg hA hB) (atom1948Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1949Coded_nonneg g hg hA hB) (atom1950Coded_nonneg g hg hA hB)) (add_nonneg (atom1951Coded_nonneg g hg hA hB) (add_nonneg (atom1952Coded_nonneg g hg hA hB) (atom1953Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1954Coded_nonneg g hg hA hB) (atom1955Coded_nonneg g hg hA hB)) (add_nonneg (atom1956Coded_nonneg g hg hA hB) (add_nonneg (atom1957Coded_nonneg g hg hA hB) (atom1958Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1959Coded_nonneg g hg hA hB) (atom1960Coded_nonneg g hg hA hB)) (add_nonneg (atom1961Coded_nonneg g hg hA hB) (add_nonneg (atom1962Coded_nonneg g hg hA hB) (atom1963Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1964Coded_nonneg g hg hA hB) (atom1965Coded_nonneg g hg hA hB)) (add_nonneg (atom1966Coded_nonneg g hg hA hB) (add_nonneg (atom1967Coded_nonneg g hg hA hB) (atom1968Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
