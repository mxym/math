-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1889 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1889Coded : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 1))]
theorem atom1889Coded_decode : atom1889 = SparsePolynomial.decodeCubic 24 atom1889Coded := by decide +kernel
theorem atom1889Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) := by
  have h := atom1889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1890 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1890 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202067913062400 : Int) atom1890) := by
  rw [SparsePolynomial.eval_scale, eval_atom1890]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1890Coded : CoefficientMerge.Poly := [(nat_lit 4482, Int.ofNat (nat_lit 1))]
theorem atom1890Coded_decode : atom1890 = SparsePolynomial.decodeCubic 24 atom1890Coded := by decide +kernel
theorem atom1890Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded) := by
  have h := atom1890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1891 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1891Coded : CoefficientMerge.Poly := [(nat_lit 4483, Int.ofNat (nat_lit 1))]
theorem atom1891Coded_decode : atom1891 = SparsePolynomial.decodeCubic 24 atom1891Coded := by decide +kernel
theorem atom1891Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) := by
  have h := atom1891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1892 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1892Coded : CoefficientMerge.Poly := [(nat_lit 4484, Int.ofNat (nat_lit 1))]
theorem atom1892Coded_decode : atom1892 = SparsePolynomial.decodeCubic 24 atom1892Coded := by decide +kernel
theorem atom1892Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) := by
  have h := atom1892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1893 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1893Coded : CoefficientMerge.Poly := [(nat_lit 4485, Int.ofNat (nat_lit 1))]
theorem atom1893Coded_decode : atom1893 = SparsePolynomial.decodeCubic 24 atom1893Coded := by decide +kernel
theorem atom1893Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded) := by
  have h := atom1893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1894 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1894Coded : CoefficientMerge.Poly := [(nat_lit 4486, Int.ofNat (nat_lit 1))]
theorem atom1894Coded_decode : atom1894 = SparsePolynomial.decodeCubic 24 atom1894Coded := by decide +kernel
theorem atom1894Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) := by
  have h := atom1894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1895 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1895Coded : CoefficientMerge.Poly := [(nat_lit 4487, Int.ofNat (nat_lit 1))]
theorem atom1895Coded_decode : atom1895 = SparsePolynomial.decodeCubic 24 atom1895Coded := by decide +kernel
theorem atom1895Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded) := by
  have h := atom1895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1896 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1896 = ((g 7) * (g 19) * (g 19)) := by
  norm_num [atom1896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129207041187840 : Int) atom1896) := by
  rw [SparsePolynomial.eval_scale, eval_atom1896]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1896Coded : CoefficientMerge.Poly := [(nat_lit 4507, Int.ofNat (nat_lit 1))]
theorem atom1896Coded_decode : atom1896 = SparsePolynomial.decodeCubic 24 atom1896Coded := by decide +kernel
theorem atom1896Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) := by
  have h := atom1896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1897 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1897Coded : CoefficientMerge.Poly := [(nat_lit 4508, Int.ofNat (nat_lit 1))]
theorem atom1897Coded_decode : atom1897 = SparsePolynomial.decodeCubic 24 atom1897Coded := by decide +kernel
theorem atom1897Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) := by
  have h := atom1897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1898 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1898Coded : CoefficientMerge.Poly := [(nat_lit 4509, Int.ofNat (nat_lit 1))]
theorem atom1898Coded_decode : atom1898 = SparsePolynomial.decodeCubic 24 atom1898Coded := by decide +kernel
theorem atom1898Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded) := by
  have h := atom1898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1899 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1899Coded : CoefficientMerge.Poly := [(nat_lit 4510, Int.ofNat (nat_lit 1))]
theorem atom1899Coded_decode : atom1899 = SparsePolynomial.decodeCubic 24 atom1899Coded := by decide +kernel
theorem atom1899Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) := by
  have h := atom1899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1900 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1900Coded : CoefficientMerge.Poly := [(nat_lit 4511, Int.ofNat (nat_lit 1))]
theorem atom1900Coded_decode : atom1900 = SparsePolynomial.decodeCubic 24 atom1900Coded := by decide +kernel
theorem atom1900Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded) := by
  have h := atom1900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1901 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1901 = ((g 7) * (g 20) * (g 20)) := by
  norm_num [atom1901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309267950745600 : Int) atom1901) := by
  rw [SparsePolynomial.eval_scale, eval_atom1901]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1901Coded : CoefficientMerge.Poly := [(nat_lit 4532, Int.ofNat (nat_lit 1))]
theorem atom1901Coded_decode : atom1901 = SparsePolynomial.decodeCubic 24 atom1901Coded := by decide +kernel
theorem atom1901Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) := by
  have h := atom1901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1902 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1902Coded : CoefficientMerge.Poly := [(nat_lit 4533, Int.ofNat (nat_lit 1))]
theorem atom1902Coded_decode : atom1902 = SparsePolynomial.decodeCubic 24 atom1902Coded := by decide +kernel
theorem atom1902Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) := by
  have h := atom1902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1903 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1903Coded : CoefficientMerge.Poly := [(nat_lit 4534, Int.ofNat (nat_lit 1))]
theorem atom1903Coded_decode : atom1903 = SparsePolynomial.decodeCubic 24 atom1903Coded := by decide +kernel
theorem atom1903Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded) := by
  have h := atom1903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1904 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1904Coded : CoefficientMerge.Poly := [(nat_lit 4535, Int.ofNat (nat_lit 1))]
theorem atom1904Coded_decode : atom1904 = SparsePolynomial.decodeCubic 24 atom1904Coded := by decide +kernel
theorem atom1904Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) := by
  have h := atom1904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1905 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1905 = ((g 7) * (g 21) * (g 21)) := by
  norm_num [atom1905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89500313548800 : Int) atom1905) := by
  rw [SparsePolynomial.eval_scale, eval_atom1905]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1905Coded : CoefficientMerge.Poly := [(nat_lit 4557, Int.ofNat (nat_lit 1))]
theorem atom1905Coded_decode : atom1905 = SparsePolynomial.decodeCubic 24 atom1905Coded := by decide +kernel
theorem atom1905Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded) := by
  have h := atom1905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1906 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1906Coded : CoefficientMerge.Poly := [(nat_lit 4558, Int.ofNat (nat_lit 1))]
theorem atom1906Coded_decode : atom1906 = SparsePolynomial.decodeCubic 24 atom1906Coded := by decide +kernel
theorem atom1906Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) := by
  have h := atom1906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1907 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1907Coded : CoefficientMerge.Poly := [(nat_lit 4559, Int.ofNat (nat_lit 1))]
theorem atom1907Coded_decode : atom1907 = SparsePolynomial.decodeCubic 24 atom1907Coded := by decide +kernel
theorem atom1907Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) := by
  have h := atom1907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1908 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1908 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15968023948800 : Int) atom1908) := by
  rw [SparsePolynomial.eval_scale, eval_atom1908]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1908Coded : CoefficientMerge.Poly := [(nat_lit 4808, Int.ofNat (nat_lit 1))]
theorem atom1908Coded_decode : atom1908 = SparsePolynomial.decodeCubic 24 atom1908Coded := by decide +kernel
theorem atom1908Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded) := by
  have h := atom1908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1909 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1909 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30188327122800 : Int) atom1909) := by
  rw [SparsePolynomial.eval_scale, eval_atom1909]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1909Coded : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 1))]
theorem atom1909Coded_decode : atom1909 = SparsePolynomial.decodeCubic 24 atom1909Coded := by decide +kernel
theorem atom1909Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) := by
  have h := atom1909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1910 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1910 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2502889795296 : Int) atom1910) := by
  rw [SparsePolynomial.eval_scale, eval_atom1910]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1910Coded : CoefficientMerge.Poly := [(nat_lit 4810, Int.ofNat (nat_lit 1))]
theorem atom1910Coded_decode : atom1910 = SparsePolynomial.decodeCubic 24 atom1910Coded := by decide +kernel
theorem atom1910Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded) := by
  have h := atom1910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1911 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1911 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1911) := by
  rw [SparsePolynomial.eval_scale, eval_atom1911]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1911Coded : CoefficientMerge.Poly := [(nat_lit 4811, Int.ofNat (nat_lit 1))]
theorem atom1911Coded_decode : atom1911 = SparsePolynomial.decodeCubic 24 atom1911Coded := by decide +kernel
theorem atom1911Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) := by
  have h := atom1911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1912 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1912 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35074459173600 : Int) atom1912) := by
  rw [SparsePolynomial.eval_scale, eval_atom1912]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1912Coded : CoefficientMerge.Poly := [(nat_lit 4833, Int.ofNat (nat_lit 1))]
theorem atom1912Coded_decode : atom1912 = SparsePolynomial.decodeCubic 24 atom1912Coded := by decide +kernel
theorem atom1912Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) := by
  have h := atom1912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1913 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom1913Coded : CoefficientMerge.Poly := [(nat_lit 4834, Int.ofNat (nat_lit 1))]
theorem atom1913Coded_decode : atom1913 = SparsePolynomial.decodeCubic 24 atom1913Coded := by decide +kernel
theorem atom1913Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded) := by
  have h := atom1913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1914 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1914Coded : CoefficientMerge.Poly := [(nat_lit 4838, Int.ofNat (nat_lit 1))]
theorem atom1914Coded_decode : atom1914 = SparsePolynomial.decodeCubic 24 atom1914Coded := by decide +kernel
theorem atom1914Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) := by
  have h := atom1914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1915 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1915Coded : CoefficientMerge.Poly := [(nat_lit 4839, Int.ofNat (nat_lit 1))]
theorem atom1915Coded_decode : atom1915 = SparsePolynomial.decodeCubic 24 atom1915Coded := by decide +kernel
theorem atom1915Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded) := by
  have h := atom1915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1916 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1916Coded : CoefficientMerge.Poly := [(nat_lit 4840, Int.ofNat (nat_lit 1))]
theorem atom1916Coded_decode : atom1916 = SparsePolynomial.decodeCubic 24 atom1916Coded := by decide +kernel
theorem atom1916Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) := by
  have h := atom1916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1917 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1917Coded : CoefficientMerge.Poly := [(nat_lit 4841, Int.ofNat (nat_lit 1))]
theorem atom1917Coded_decode : atom1917 = SparsePolynomial.decodeCubic 24 atom1917Coded := by decide +kernel
theorem atom1917Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) := by
  have h := atom1917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1918 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1918Coded : CoefficientMerge.Poly := [(nat_lit 4843, Int.ofNat (nat_lit 1))]
theorem atom1918Coded_decode : atom1918 = SparsePolynomial.decodeCubic 24 atom1918Coded := by decide +kernel
theorem atom1918Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded) := by
  have h := atom1918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1919 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1919Coded : CoefficientMerge.Poly := [(nat_lit 4845, Int.ofNat (nat_lit 1))]
theorem atom1919Coded_decode : atom1919 = SparsePolynomial.decodeCubic 24 atom1919Coded := by decide +kernel
theorem atom1919Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) := by
  have h := atom1919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1920 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1920Coded : CoefficientMerge.Poly := [(nat_lit 4846, Int.ofNat (nat_lit 1))]
theorem atom1920Coded_decode : atom1920 = SparsePolynomial.decodeCubic 24 atom1920Coded := by decide +kernel
theorem atom1920Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded) := by
  have h := atom1920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1921 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1921Coded : CoefficientMerge.Poly := [(nat_lit 4847, Int.ofNat (nat_lit 1))]
theorem atom1921Coded_decode : atom1921 = SparsePolynomial.decodeCubic 24 atom1921Coded := by decide +kernel
theorem atom1921Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) := by
  have h := atom1921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1922 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1922 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5326574012496 : Int) atom1922) := by
  rw [SparsePolynomial.eval_scale, eval_atom1922]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1922Coded : CoefficientMerge.Poly := [(nat_lit 4858, Int.ofNat (nat_lit 1))]
theorem atom1922Coded_decode : atom1922 = SparsePolynomial.decodeCubic 24 atom1922Coded := by decide +kernel
theorem atom1922Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) := by
  have h := atom1922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1923 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom1923Coded : CoefficientMerge.Poly := [(nat_lit 4859, Int.ofNat (nat_lit 1))]
theorem atom1923Coded_decode : atom1923 = SparsePolynomial.decodeCubic 24 atom1923Coded := by decide +kernel
theorem atom1923Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded) := by
  have h := atom1923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1924 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1924Coded : CoefficientMerge.Poly := [(nat_lit 4860, Int.ofNat (nat_lit 1))]
theorem atom1924Coded_decode : atom1924 = SparsePolynomial.decodeCubic 24 atom1924Coded := by decide +kernel
theorem atom1924Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) := by
  have h := atom1924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1925 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1925Coded : CoefficientMerge.Poly := [(nat_lit 4861, Int.ofNat (nat_lit 1))]
theorem atom1925Coded_decode : atom1925 = SparsePolynomial.decodeCubic 24 atom1925Coded := by decide +kernel
theorem atom1925Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded) := by
  have h := atom1925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1926 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1926Coded : CoefficientMerge.Poly := [(nat_lit 4862, Int.ofNat (nat_lit 1))]
theorem atom1926Coded_decode : atom1926 = SparsePolynomial.decodeCubic 24 atom1926Coded := by decide +kernel
theorem atom1926Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) := by
  have h := atom1926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1927 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1927Coded : CoefficientMerge.Poly := [(nat_lit 4863, Int.ofNat (nat_lit 1))]
theorem atom1927Coded_decode : atom1927 = SparsePolynomial.decodeCubic 24 atom1927Coded := by decide +kernel
theorem atom1927Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) := by
  have h := atom1927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1928 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1928Coded : CoefficientMerge.Poly := [(nat_lit 4864, Int.ofNat (nat_lit 1))]
theorem atom1928Coded_decode : atom1928 = SparsePolynomial.decodeCubic 24 atom1928Coded := by decide +kernel
theorem atom1928Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded) := by
  have h := atom1928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1929 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1929Coded : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 1))]
theorem atom1929Coded_decode : atom1929 = SparsePolynomial.decodeCubic 24 atom1929Coded := by decide +kernel
theorem atom1929Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) := by
  have h := atom1929_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1929Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1930 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1930Coded : CoefficientMerge.Poly := [(nat_lit 4866, Int.ofNat (nat_lit 1))]
theorem atom1930Coded_decode : atom1930 = SparsePolynomial.decodeCubic 24 atom1930Coded := by decide +kernel
theorem atom1930Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded) := by
  have h := atom1930_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1930Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1931 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1931Coded : CoefficientMerge.Poly := [(nat_lit 4869, Int.ofNat (nat_lit 1))]
theorem atom1931Coded_decode : atom1931 = SparsePolynomial.decodeCubic 24 atom1931Coded := by decide +kernel
theorem atom1931Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) := by
  have h := atom1931_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1931Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1932 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1932Coded : CoefficientMerge.Poly := [(nat_lit 4870, Int.ofNat (nat_lit 1))]
theorem atom1932Coded_decode : atom1932 = SparsePolynomial.decodeCubic 24 atom1932Coded := by decide +kernel
theorem atom1932Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) := by
  have h := atom1932_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1932Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1933 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1933Coded : CoefficientMerge.Poly := [(nat_lit 4871, Int.ofNat (nat_lit 1))]
theorem atom1933Coded_decode : atom1933 = SparsePolynomial.decodeCubic 24 atom1933Coded := by decide +kernel
theorem atom1933Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded) := by
  have h := atom1933_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1933Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1934 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1934 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1934 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1934_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25565759604000 : Int) atom1934) := by
  rw [SparsePolynomial.eval_scale, eval_atom1934]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1934Coded : CoefficientMerge.Poly := [(nat_lit 4883, Int.ofNat (nat_lit 1))]
theorem atom1934Coded_decode : atom1934 = SparsePolynomial.decodeCubic 24 atom1934Coded := by decide +kernel
theorem atom1934Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) := by
  have h := atom1934_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1934Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1935 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1935Coded : CoefficientMerge.Poly := [(nat_lit 4884, Int.ofNat (nat_lit 1))]
theorem atom1935Coded_decode : atom1935 = SparsePolynomial.decodeCubic 24 atom1935Coded := by decide +kernel
theorem atom1935Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded) := by
  have h := atom1935_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1935Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1936 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1936Coded : CoefficientMerge.Poly := [(nat_lit 4885, Int.ofNat (nat_lit 1))]
theorem atom1936Coded_decode : atom1936 = SparsePolynomial.decodeCubic 24 atom1936Coded := by decide +kernel
theorem atom1936Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) := by
  have h := atom1936_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1936Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1937 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1937Coded : CoefficientMerge.Poly := [(nat_lit 4886, Int.ofNat (nat_lit 1))]
theorem atom1937Coded_decode : atom1937 = SparsePolynomial.decodeCubic 24 atom1937Coded := by decide +kernel
theorem atom1937Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) := by
  have h := atom1937_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1937Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1938 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1938Coded : CoefficientMerge.Poly := [(nat_lit 4887, Int.ofNat (nat_lit 1))]
theorem atom1938Coded_decode : atom1938 = SparsePolynomial.decodeCubic 24 atom1938Coded := by decide +kernel
theorem atom1938Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded) := by
  have h := atom1938_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1938Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1939 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1939Coded : CoefficientMerge.Poly := [(nat_lit 4888, Int.ofNat (nat_lit 1))]
theorem atom1939Coded_decode : atom1939 = SparsePolynomial.decodeCubic 24 atom1939Coded := by decide +kernel
theorem atom1939Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) := by
  have h := atom1939_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1939Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1940 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1940Coded : CoefficientMerge.Poly := [(nat_lit 4889, Int.ofNat (nat_lit 1))]
theorem atom1940Coded_decode : atom1940 = SparsePolynomial.decodeCubic 24 atom1940Coded := by decide +kernel
theorem atom1940Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded) := by
  have h := atom1940_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1940Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1941 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1941Coded : CoefficientMerge.Poly := [(nat_lit 4890, Int.ofNat (nat_lit 1))]
theorem atom1941Coded_decode : atom1941 = SparsePolynomial.decodeCubic 24 atom1941Coded := by decide +kernel
theorem atom1941Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) := by
  have h := atom1941_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1941Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1942 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1942Coded : CoefficientMerge.Poly := [(nat_lit 4891, Int.ofNat (nat_lit 1))]
theorem atom1942Coded_decode : atom1942 = SparsePolynomial.decodeCubic 24 atom1942Coded := by decide +kernel
theorem atom1942Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) := by
  have h := atom1942_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1942Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1943 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1943Coded : CoefficientMerge.Poly := [(nat_lit 4892, Int.ofNat (nat_lit 1))]
theorem atom1943Coded_decode : atom1943 = SparsePolynomial.decodeCubic 24 atom1943Coded := by decide +kernel
theorem atom1943Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded) := by
  have h := atom1943_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1943Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1944 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1944Coded : CoefficientMerge.Poly := [(nat_lit 4893, Int.ofNat (nat_lit 1))]
theorem atom1944Coded_decode : atom1944 = SparsePolynomial.decodeCubic 24 atom1944Coded := by decide +kernel
theorem atom1944Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) := by
  have h := atom1944_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1944Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1945 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1945Coded : CoefficientMerge.Poly := [(nat_lit 4894, Int.ofNat (nat_lit 1))]
theorem atom1945Coded_decode : atom1945 = SparsePolynomial.decodeCubic 24 atom1945Coded := by decide +kernel
theorem atom1945Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded) := by
  have h := atom1945_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1945Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1946 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1946Coded : CoefficientMerge.Poly := [(nat_lit 4895, Int.ofNat (nat_lit 1))]
theorem atom1946Coded_decode : atom1946 = SparsePolynomial.decodeCubic 24 atom1946Coded := by decide +kernel
theorem atom1946Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) := by
  have h := atom1946_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1946Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1947 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1947 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1947 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1947_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34577008804800 : Int) atom1947) := by
  rw [SparsePolynomial.eval_scale, eval_atom1947]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1947Coded : CoefficientMerge.Poly := [(nat_lit 4908, Int.ofNat (nat_lit 1))]
theorem atom1947Coded_decode : atom1947 = SparsePolynomial.decodeCubic 24 atom1947Coded := by decide +kernel
theorem atom1947Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) := by
  have h := atom1947_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1947Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1948 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1948Coded : CoefficientMerge.Poly := [(nat_lit 4909, Int.ofNat (nat_lit 1))]
theorem atom1948Coded_decode : atom1948 = SparsePolynomial.decodeCubic 24 atom1948Coded := by decide +kernel
theorem atom1948Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded) := by
  have h := atom1948_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1948Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1949 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1949Coded : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 1))]
theorem atom1949Coded_decode : atom1949 = SparsePolynomial.decodeCubic 24 atom1949Coded := by decide +kernel
theorem atom1949Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) := by
  have h := atom1949_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1949Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1950 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1950Coded : CoefficientMerge.Poly := [(nat_lit 4911, Int.ofNat (nat_lit 1))]
theorem atom1950Coded_decode : atom1950 = SparsePolynomial.decodeCubic 24 atom1950Coded := by decide +kernel
theorem atom1950Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded) := by
  have h := atom1950_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1950Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1951 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1951Coded : CoefficientMerge.Poly := [(nat_lit 4912, Int.ofNat (nat_lit 1))]
theorem atom1951Coded_decode : atom1951 = SparsePolynomial.decodeCubic 24 atom1951Coded := by decide +kernel
theorem atom1951Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) := by
  have h := atom1951_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1951Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1952 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1952Coded : CoefficientMerge.Poly := [(nat_lit 4913, Int.ofNat (nat_lit 1))]
theorem atom1952Coded_decode : atom1952 = SparsePolynomial.decodeCubic 24 atom1952Coded := by decide +kernel
theorem atom1952Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) := by
  have h := atom1952_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1952Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1953 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1953Coded : CoefficientMerge.Poly := [(nat_lit 4914, Int.ofNat (nat_lit 1))]
theorem atom1953Coded_decode : atom1953 = SparsePolynomial.decodeCubic 24 atom1953Coded := by decide +kernel
theorem atom1953Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded) := by
  have h := atom1953_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1953Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1954 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1954Coded : CoefficientMerge.Poly := [(nat_lit 4915, Int.ofNat (nat_lit 1))]
theorem atom1954Coded_decode : atom1954 = SparsePolynomial.decodeCubic 24 atom1954Coded := by decide +kernel
theorem atom1954Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) := by
  have h := atom1954_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1954Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1955 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1955Coded : CoefficientMerge.Poly := [(nat_lit 4916, Int.ofNat (nat_lit 1))]
theorem atom1955Coded_decode : atom1955 = SparsePolynomial.decodeCubic 24 atom1955Coded := by decide +kernel
theorem atom1955Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded) := by
  have h := atom1955_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1955Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1956 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1956Coded : CoefficientMerge.Poly := [(nat_lit 4917, Int.ofNat (nat_lit 1))]
theorem atom1956Coded_decode : atom1956 = SparsePolynomial.decodeCubic 24 atom1956Coded := by decide +kernel
theorem atom1956Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) := by
  have h := atom1956_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1956Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1957 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1957Coded : CoefficientMerge.Poly := [(nat_lit 4918, Int.ofNat (nat_lit 1))]
theorem atom1957Coded_decode : atom1957 = SparsePolynomial.decodeCubic 24 atom1957Coded := by decide +kernel
theorem atom1957Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) := by
  have h := atom1957_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1957Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1958 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom1958Coded : CoefficientMerge.Poly := [(nat_lit 4919, Int.ofNat (nat_lit 1))]
theorem atom1958Coded_decode : atom1958 = SparsePolynomial.decodeCubic 24 atom1958Coded := by decide +kernel
theorem atom1958Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded) := by
  have h := atom1958_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1958Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1959 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1959 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1959 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1959_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57739680028800 : Int) atom1959) := by
  rw [SparsePolynomial.eval_scale, eval_atom1959]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1959Coded : CoefficientMerge.Poly := [(nat_lit 4933, Int.ofNat (nat_lit 1))]
theorem atom1959Coded_decode : atom1959 = SparsePolynomial.decodeCubic 24 atom1959Coded := by decide +kernel
theorem atom1959Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) := by
  have h := atom1959_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1959Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1960 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1960Coded : CoefficientMerge.Poly := [(nat_lit 4934, Int.ofNat (nat_lit 1))]
theorem atom1960Coded_decode : atom1960 = SparsePolynomial.decodeCubic 24 atom1960Coded := by decide +kernel
theorem atom1960Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded) := by
  have h := atom1960_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1960Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1961 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1961Coded : CoefficientMerge.Poly := [(nat_lit 4935, Int.ofNat (nat_lit 1))]
theorem atom1961Coded_decode : atom1961 = SparsePolynomial.decodeCubic 24 atom1961Coded := by decide +kernel
theorem atom1961Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) := by
  have h := atom1961_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1961Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1962 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1962Coded : CoefficientMerge.Poly := [(nat_lit 4936, Int.ofNat (nat_lit 1))]
theorem atom1962Coded_decode : atom1962 = SparsePolynomial.decodeCubic 24 atom1962Coded := by decide +kernel
theorem atom1962Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) := by
  have h := atom1962_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1962Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1963 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1963Coded : CoefficientMerge.Poly := [(nat_lit 4937, Int.ofNat (nat_lit 1))]
theorem atom1963Coded_decode : atom1963 = SparsePolynomial.decodeCubic 24 atom1963Coded := by decide +kernel
theorem atom1963Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded) := by
  have h := atom1963_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1963Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1964 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1964Coded : CoefficientMerge.Poly := [(nat_lit 4938, Int.ofNat (nat_lit 1))]
theorem atom1964Coded_decode : atom1964 = SparsePolynomial.decodeCubic 24 atom1964Coded := by decide +kernel
theorem atom1964Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) := by
  have h := atom1964_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1964Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1965 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1965Coded : CoefficientMerge.Poly := [(nat_lit 4939, Int.ofNat (nat_lit 1))]
theorem atom1965Coded_decode : atom1965 = SparsePolynomial.decodeCubic 24 atom1965Coded := by decide +kernel
theorem atom1965Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded) := by
  have h := atom1965_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1965Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1966 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1966Coded : CoefficientMerge.Poly := [(nat_lit 4940, Int.ofNat (nat_lit 1))]
theorem atom1966Coded_decode : atom1966 = SparsePolynomial.decodeCubic 24 atom1966Coded := by decide +kernel
theorem atom1966Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) := by
  have h := atom1966_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1966Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1967 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom1967Coded : CoefficientMerge.Poly := [(nat_lit 4941, Int.ofNat (nat_lit 1))]
theorem atom1967Coded_decode : atom1967 = SparsePolynomial.decodeCubic 24 atom1967Coded := by decide +kernel
theorem atom1967Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) := by
  have h := atom1967_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1967Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1968 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom1968Coded : CoefficientMerge.Poly := [(nat_lit 4942, Int.ofNat (nat_lit 1))]
theorem atom1968Coded_decode : atom1968 = SparsePolynomial.decodeCubic 24 atom1968Coded := by decide +kernel
theorem atom1968Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded) := by
  have h := atom1968_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1968Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block026 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200)), (nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800)), (nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400)), (nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096)), (nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800)), (nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200)), (nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600)), (nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
def block026_data_flat000 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800))]
theorem block026_data_flat000_step : block026_data_flat000 = (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) := by decide +kernel
theorem block026_data_flat000_original : block026_data_flat000 = (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) := by
  rw [block026_data_flat000_step]
def block026_data_flat001 : CoefficientMerge.Poly := [(nat_lit 4482, Int.ofNat (nat_lit 202067913062400))]
theorem block026_data_flat001_step : block026_data_flat001 = (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded) := by decide +kernel
theorem block026_data_flat001_original : block026_data_flat001 = (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded) := by
  rw [block026_data_flat001_step]
def block026_data_flat002 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400))]
theorem block026_data_flat002_step : block026_data_flat002 = (CoefficientMerge.fastMerge block026_data_flat000 block026_data_flat001) := by decide +kernel
theorem block026_data_flat002_original : block026_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) := by
  rw [block026_data_flat002_step, block026_data_flat000_original, block026_data_flat001_original]
def block026_data_flat003 : CoefficientMerge.Poly := [(nat_lit 4483, Int.ofNat (nat_lit 390017626521600))]
theorem block026_data_flat003_step : block026_data_flat003 = (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) := by decide +kernel
theorem block026_data_flat003_original : block026_data_flat003 = (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) := by
  rw [block026_data_flat003_step]
def block026_data_flat004 : CoefficientMerge.Poly := [(nat_lit 4484, Int.ofNat (nat_lit 587162124595200))]
theorem block026_data_flat004_step : block026_data_flat004 = (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) := by decide +kernel
theorem block026_data_flat004_original : block026_data_flat004 = (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) := by
  rw [block026_data_flat004_step]
def block026_data_flat005 : CoefficientMerge.Poly := [(nat_lit 4485, Int.ofNat (nat_lit 591060221875200))]
theorem block026_data_flat005_step : block026_data_flat005 = (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded) := by decide +kernel
theorem block026_data_flat005_original : block026_data_flat005 = (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded) := by
  rw [block026_data_flat005_step]
def block026_data_flat006 : CoefficientMerge.Poly := [(nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200))]
theorem block026_data_flat006_step : block026_data_flat006 = (CoefficientMerge.fastMerge block026_data_flat004 block026_data_flat005) := by decide +kernel
theorem block026_data_flat006_original : block026_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)) := by
  rw [block026_data_flat006_step, block026_data_flat004_original, block026_data_flat005_original]
def block026_data_flat007 : CoefficientMerge.Poly := [(nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200))]
theorem block026_data_flat007_step : block026_data_flat007 = (CoefficientMerge.fastMerge block026_data_flat003 block026_data_flat006) := by decide +kernel
theorem block026_data_flat007_original : block026_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded))) := by
  rw [block026_data_flat007_step, block026_data_flat003_original, block026_data_flat006_original]
def block026_data_flat008 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200))]
theorem block026_data_flat008_step : block026_data_flat008 = (CoefficientMerge.fastMerge block026_data_flat002 block026_data_flat007) := by decide +kernel
theorem block026_data_flat008_original : block026_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) := by
  rw [block026_data_flat008_step, block026_data_flat002_original, block026_data_flat007_original]
def block026_data_flat009 : CoefficientMerge.Poly := [(nat_lit 4486, Int.ofNat (nat_lit 465720930796800))]
theorem block026_data_flat009_step : block026_data_flat009 = (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) := by decide +kernel
theorem block026_data_flat009_original : block026_data_flat009 = (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) := by
  rw [block026_data_flat009_step]
def block026_data_flat010 : CoefficientMerge.Poly := [(nat_lit 4487, Int.ofNat (nat_lit 672974601868800))]
theorem block026_data_flat010_step : block026_data_flat010 = (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded) := by decide +kernel
theorem block026_data_flat010_original : block026_data_flat010 = (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded) := by
  rw [block026_data_flat010_step]
def block026_data_flat011 : CoefficientMerge.Poly := [(nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800))]
theorem block026_data_flat011_step : block026_data_flat011 = (CoefficientMerge.fastMerge block026_data_flat009 block026_data_flat010) := by decide +kernel
theorem block026_data_flat011_original : block026_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) := by
  rw [block026_data_flat011_step, block026_data_flat009_original, block026_data_flat010_original]
def block026_data_flat012 : CoefficientMerge.Poly := [(nat_lit 4507, Int.ofNat (nat_lit 129207041187840))]
theorem block026_data_flat012_step : block026_data_flat012 = (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) := by decide +kernel
theorem block026_data_flat012_original : block026_data_flat012 = (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) := by
  rw [block026_data_flat012_step]
def block026_data_flat013 : CoefficientMerge.Poly := [(nat_lit 4508, Int.ofNat (nat_lit 426796764979200))]
theorem block026_data_flat013_step : block026_data_flat013 = (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) := by decide +kernel
theorem block026_data_flat013_original : block026_data_flat013 = (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) := by
  rw [block026_data_flat013_step]
def block026_data_flat014 : CoefficientMerge.Poly := [(nat_lit 4509, Int.ofNat (nat_lit 432844721971200))]
theorem block026_data_flat014_step : block026_data_flat014 = (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded) := by decide +kernel
theorem block026_data_flat014_original : block026_data_flat014 = (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded) := by
  rw [block026_data_flat014_step]
def block026_data_flat015 : CoefficientMerge.Poly := [(nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200))]
theorem block026_data_flat015_step : block026_data_flat015 = (CoefficientMerge.fastMerge block026_data_flat013 block026_data_flat014) := by decide +kernel
theorem block026_data_flat015_original : block026_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded)) := by
  rw [block026_data_flat015_step, block026_data_flat013_original, block026_data_flat014_original]
def block026_data_flat016 : CoefficientMerge.Poly := [(nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200))]
theorem block026_data_flat016_step : block026_data_flat016 = (CoefficientMerge.fastMerge block026_data_flat012 block026_data_flat015) := by decide +kernel
theorem block026_data_flat016_original : block026_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))) := by
  rw [block026_data_flat016_step, block026_data_flat012_original, block026_data_flat015_original]
def block026_data_flat017 : CoefficientMerge.Poly := [(nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200))]
theorem block026_data_flat017_step : block026_data_flat017 = (CoefficientMerge.fastMerge block026_data_flat011 block026_data_flat016) := by decide +kernel
theorem block026_data_flat017_original : block026_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded)))) := by
  rw [block026_data_flat017_step, block026_data_flat011_original, block026_data_flat016_original]
def block026_data_flat018 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200))]
theorem block026_data_flat018_step : block026_data_flat018 = (CoefficientMerge.fastMerge block026_data_flat008 block026_data_flat017) := by decide +kernel
theorem block026_data_flat018_original : block026_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) := by
  rw [block026_data_flat018_step, block026_data_flat008_original, block026_data_flat017_original]
def block026_data_flat019 : CoefficientMerge.Poly := [(nat_lit 4510, Int.ofNat (nat_lit 378326949996800))]
theorem block026_data_flat019_step : block026_data_flat019 = (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) := by decide +kernel
theorem block026_data_flat019_original : block026_data_flat019 = (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) := by
  rw [block026_data_flat019_step]
def block026_data_flat020 : CoefficientMerge.Poly := [(nat_lit 4511, Int.ofNat (nat_lit 440381097072000))]
theorem block026_data_flat020_step : block026_data_flat020 = (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded) := by decide +kernel
theorem block026_data_flat020_original : block026_data_flat020 = (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded) := by
  rw [block026_data_flat020_step]
def block026_data_flat021 : CoefficientMerge.Poly := [(nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000))]
theorem block026_data_flat021_step : block026_data_flat021 = (CoefficientMerge.fastMerge block026_data_flat019 block026_data_flat020) := by decide +kernel
theorem block026_data_flat021_original : block026_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) := by
  rw [block026_data_flat021_step, block026_data_flat019_original, block026_data_flat020_original]
def block026_data_flat022 : CoefficientMerge.Poly := [(nat_lit 4532, Int.ofNat (nat_lit 309267950745600))]
theorem block026_data_flat022_step : block026_data_flat022 = (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) := by decide +kernel
theorem block026_data_flat022_original : block026_data_flat022 = (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) := by
  rw [block026_data_flat022_step]
def block026_data_flat023 : CoefficientMerge.Poly := [(nat_lit 4533, Int.ofNat (nat_lit 450681470131200))]
theorem block026_data_flat023_step : block026_data_flat023 = (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) := by decide +kernel
theorem block026_data_flat023_original : block026_data_flat023 = (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) := by
  rw [block026_data_flat023_step]
def block026_data_flat024 : CoefficientMerge.Poly := [(nat_lit 4534, Int.ofNat (nat_lit 366850113996800))]
theorem block026_data_flat024_step : block026_data_flat024 = (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded) := by decide +kernel
theorem block026_data_flat024_original : block026_data_flat024 = (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded) := by
  rw [block026_data_flat024_step]
def block026_data_flat025 : CoefficientMerge.Poly := [(nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800))]
theorem block026_data_flat025_step : block026_data_flat025 = (CoefficientMerge.fastMerge block026_data_flat023 block026_data_flat024) := by decide +kernel
theorem block026_data_flat025_original : block026_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)) := by
  rw [block026_data_flat025_step, block026_data_flat023_original, block026_data_flat024_original]
def block026_data_flat026 : CoefficientMerge.Poly := [(nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800))]
theorem block026_data_flat026_step : block026_data_flat026 = (CoefficientMerge.fastMerge block026_data_flat022 block026_data_flat025) := by decide +kernel
theorem block026_data_flat026_original : block026_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded))) := by
  rw [block026_data_flat026_step, block026_data_flat022_original, block026_data_flat025_original]
def block026_data_flat027 : CoefficientMerge.Poly := [(nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800))]
theorem block026_data_flat027_step : block026_data_flat027 = (CoefficientMerge.fastMerge block026_data_flat021 block026_data_flat026) := by decide +kernel
theorem block026_data_flat027_original : block026_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) := by
  rw [block026_data_flat027_step, block026_data_flat021_original, block026_data_flat026_original]
def block026_data_flat028 : CoefficientMerge.Poly := [(nat_lit 4535, Int.ofNat (nat_lit 455881349347200))]
theorem block026_data_flat028_step : block026_data_flat028 = (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) := by decide +kernel
theorem block026_data_flat028_original : block026_data_flat028 = (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) := by
  rw [block026_data_flat028_step]
def block026_data_flat029 : CoefficientMerge.Poly := [(nat_lit 4557, Int.ofNat (nat_lit 89500313548800))]
theorem block026_data_flat029_step : block026_data_flat029 = (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded) := by decide +kernel
theorem block026_data_flat029_original : block026_data_flat029 = (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded) := by
  rw [block026_data_flat029_step]
def block026_data_flat030 : CoefficientMerge.Poly := [(nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800))]
theorem block026_data_flat030_step : block026_data_flat030 = (CoefficientMerge.fastMerge block026_data_flat028 block026_data_flat029) := by decide +kernel
theorem block026_data_flat030_original : block026_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) := by
  rw [block026_data_flat030_step, block026_data_flat028_original, block026_data_flat029_original]
def block026_data_flat031 : CoefficientMerge.Poly := [(nat_lit 4558, Int.ofNat (nat_lit 153592979366400))]
theorem block026_data_flat031_step : block026_data_flat031 = (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) := by decide +kernel
theorem block026_data_flat031_original : block026_data_flat031 = (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) := by
  rw [block026_data_flat031_step]
def block026_data_flat032 : CoefficientMerge.Poly := [(nat_lit 4559, Int.ofNat (nat_lit 236387787048000))]
theorem block026_data_flat032_step : block026_data_flat032 = (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) := by decide +kernel
theorem block026_data_flat032_original : block026_data_flat032 = (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) := by
  rw [block026_data_flat032_step]
def block026_data_flat033 : CoefficientMerge.Poly := [(nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat033_step : block026_data_flat033 = (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded) := by decide +kernel
theorem block026_data_flat033_original : block026_data_flat033 = (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded) := by
  rw [block026_data_flat033_step]
def block026_data_flat034 : CoefficientMerge.Poly := [(nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat034_step : block026_data_flat034 = (CoefficientMerge.fastMerge block026_data_flat032 block026_data_flat033) := by decide +kernel
theorem block026_data_flat034_original : block026_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)) := by
  rw [block026_data_flat034_step, block026_data_flat032_original, block026_data_flat033_original]
def block026_data_flat035 : CoefficientMerge.Poly := [(nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat035_step : block026_data_flat035 = (CoefficientMerge.fastMerge block026_data_flat031 block026_data_flat034) := by decide +kernel
theorem block026_data_flat035_original : block026_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded))) := by
  rw [block026_data_flat035_step, block026_data_flat031_original, block026_data_flat034_original]
def block026_data_flat036 : CoefficientMerge.Poly := [(nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat036_step : block026_data_flat036 = (CoefficientMerge.fastMerge block026_data_flat030 block026_data_flat035) := by decide +kernel
theorem block026_data_flat036_original : block026_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))) := by
  rw [block026_data_flat036_step, block026_data_flat030_original, block026_data_flat035_original]
def block026_data_flat037 : CoefficientMerge.Poly := [(nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat037_step : block026_data_flat037 = (CoefficientMerge.fastMerge block026_data_flat027 block026_data_flat036) := by decide +kernel
theorem block026_data_flat037_original : block026_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded))))) := by
  rw [block026_data_flat037_step, block026_data_flat027_original, block026_data_flat036_original]
def block026_data_flat038 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200)), (nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800))]
theorem block026_data_flat038_step : block026_data_flat038 = (CoefficientMerge.fastMerge block026_data_flat018 block026_data_flat037) := by decide +kernel
theorem block026_data_flat038_original : block026_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) := by
  rw [block026_data_flat038_step, block026_data_flat018_original, block026_data_flat037_original]
def block026_data_flat039 : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 30188327122800))]
theorem block026_data_flat039_step : block026_data_flat039 = (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) := by decide +kernel
theorem block026_data_flat039_original : block026_data_flat039 = (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) := by
  rw [block026_data_flat039_step]
def block026_data_flat040 : CoefficientMerge.Poly := [(nat_lit 4810, Int.ofNat (nat_lit 2502889795296))]
theorem block026_data_flat040_step : block026_data_flat040 = (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded) := by decide +kernel
theorem block026_data_flat040_original : block026_data_flat040 = (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded) := by
  rw [block026_data_flat040_step]
def block026_data_flat041 : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296))]
theorem block026_data_flat041_step : block026_data_flat041 = (CoefficientMerge.fastMerge block026_data_flat039 block026_data_flat040) := by decide +kernel
theorem block026_data_flat041_original : block026_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) := by
  rw [block026_data_flat041_step, block026_data_flat039_original, block026_data_flat040_original]
def block026_data_flat042 : CoefficientMerge.Poly := [(nat_lit 4811, Int.ofNat (nat_lit 3083040576000))]
theorem block026_data_flat042_step : block026_data_flat042 = (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) := by decide +kernel
theorem block026_data_flat042_original : block026_data_flat042 = (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) := by
  rw [block026_data_flat042_step]
def block026_data_flat043 : CoefficientMerge.Poly := [(nat_lit 4833, Int.ofNat (nat_lit 35074459173600))]
theorem block026_data_flat043_step : block026_data_flat043 = (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) := by decide +kernel
theorem block026_data_flat043_original : block026_data_flat043 = (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) := by
  rw [block026_data_flat043_step]
def block026_data_flat044 : CoefficientMerge.Poly := [(nat_lit 4834, Int.ofNat (nat_lit 17799156411696))]
theorem block026_data_flat044_step : block026_data_flat044 = (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded) := by decide +kernel
theorem block026_data_flat044_original : block026_data_flat044 = (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded) := by
  rw [block026_data_flat044_step]
def block026_data_flat045 : CoefficientMerge.Poly := [(nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696))]
theorem block026_data_flat045_step : block026_data_flat045 = (CoefficientMerge.fastMerge block026_data_flat043 block026_data_flat044) := by decide +kernel
theorem block026_data_flat045_original : block026_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)) := by
  rw [block026_data_flat045_step, block026_data_flat043_original, block026_data_flat044_original]
def block026_data_flat046 : CoefficientMerge.Poly := [(nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696))]
theorem block026_data_flat046_step : block026_data_flat046 = (CoefficientMerge.fastMerge block026_data_flat042 block026_data_flat045) := by decide +kernel
theorem block026_data_flat046_original : block026_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded))) := by
  rw [block026_data_flat046_step, block026_data_flat042_original, block026_data_flat045_original]
def block026_data_flat047 : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696))]
theorem block026_data_flat047_step : block026_data_flat047 = (CoefficientMerge.fastMerge block026_data_flat041 block026_data_flat046) := by decide +kernel
theorem block026_data_flat047_original : block026_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) := by
  rw [block026_data_flat047_step, block026_data_flat041_original, block026_data_flat046_original]
def block026_data_flat048 : CoefficientMerge.Poly := [(nat_lit 4838, Int.ofNat (nat_lit 3083040576000))]
theorem block026_data_flat048_step : block026_data_flat048 = (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) := by decide +kernel
theorem block026_data_flat048_original : block026_data_flat048 = (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) := by
  rw [block026_data_flat048_step]
def block026_data_flat049 : CoefficientMerge.Poly := [(nat_lit 4839, Int.ofNat (nat_lit 6166081152000))]
theorem block026_data_flat049_step : block026_data_flat049 = (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded) := by decide +kernel
theorem block026_data_flat049_original : block026_data_flat049 = (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded) := by
  rw [block026_data_flat049_step]
def block026_data_flat050 : CoefficientMerge.Poly := [(nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000))]
theorem block026_data_flat050_step : block026_data_flat050 = (CoefficientMerge.fastMerge block026_data_flat048 block026_data_flat049) := by decide +kernel
theorem block026_data_flat050_original : block026_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) := by
  rw [block026_data_flat050_step, block026_data_flat048_original, block026_data_flat049_original]
def block026_data_flat051 : CoefficientMerge.Poly := [(nat_lit 4840, Int.ofNat (nat_lit 9249121728000))]
theorem block026_data_flat051_step : block026_data_flat051 = (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) := by decide +kernel
theorem block026_data_flat051_original : block026_data_flat051 = (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) := by
  rw [block026_data_flat051_step]
def block026_data_flat052 : CoefficientMerge.Poly := [(nat_lit 4841, Int.ofNat (nat_lit 12332162304000))]
theorem block026_data_flat052_step : block026_data_flat052 = (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) := by decide +kernel
theorem block026_data_flat052_original : block026_data_flat052 = (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) := by
  rw [block026_data_flat052_step]
def block026_data_flat053 : CoefficientMerge.Poly := [(nat_lit 4843, Int.ofNat (nat_lit 1197778982400))]
theorem block026_data_flat053_step : block026_data_flat053 = (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded) := by decide +kernel
theorem block026_data_flat053_original : block026_data_flat053 = (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded) := by
  rw [block026_data_flat053_step]
def block026_data_flat054 : CoefficientMerge.Poly := [(nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400))]
theorem block026_data_flat054_step : block026_data_flat054 = (CoefficientMerge.fastMerge block026_data_flat052 block026_data_flat053) := by decide +kernel
theorem block026_data_flat054_original : block026_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded)) := by
  rw [block026_data_flat054_step, block026_data_flat052_original, block026_data_flat053_original]
def block026_data_flat055 : CoefficientMerge.Poly := [(nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400))]
theorem block026_data_flat055_step : block026_data_flat055 = (CoefficientMerge.fastMerge block026_data_flat051 block026_data_flat054) := by decide +kernel
theorem block026_data_flat055_original : block026_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))) := by
  rw [block026_data_flat055_step, block026_data_flat051_original, block026_data_flat054_original]
def block026_data_flat056 : CoefficientMerge.Poly := [(nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400))]
theorem block026_data_flat056_step : block026_data_flat056 = (CoefficientMerge.fastMerge block026_data_flat050 block026_data_flat055) := by decide +kernel
theorem block026_data_flat056_original : block026_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded)))) := by
  rw [block026_data_flat056_step, block026_data_flat050_original, block026_data_flat055_original]
def block026_data_flat057 : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400))]
theorem block026_data_flat057_step : block026_data_flat057 = (CoefficientMerge.fastMerge block026_data_flat047 block026_data_flat056) := by decide +kernel
theorem block026_data_flat057_original : block026_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) := by
  rw [block026_data_flat057_step, block026_data_flat047_original, block026_data_flat056_original]
def block026_data_flat058 : CoefficientMerge.Poly := [(nat_lit 4845, Int.ofNat (nat_lit 45125791603200))]
theorem block026_data_flat058_step : block026_data_flat058 = (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) := by decide +kernel
theorem block026_data_flat058_original : block026_data_flat058 = (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) := by
  rw [block026_data_flat058_step]
def block026_data_flat059 : CoefficientMerge.Poly := [(nat_lit 4846, Int.ofNat (nat_lit 87856025241600))]
theorem block026_data_flat059_step : block026_data_flat059 = (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded) := by decide +kernel
theorem block026_data_flat059_original : block026_data_flat059 = (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded) := by
  rw [block026_data_flat059_step]
def block026_data_flat060 : CoefficientMerge.Poly := [(nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600))]
theorem block026_data_flat060_step : block026_data_flat060 = (CoefficientMerge.fastMerge block026_data_flat058 block026_data_flat059) := by decide +kernel
theorem block026_data_flat060_original : block026_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) := by
  rw [block026_data_flat060_step, block026_data_flat058_original, block026_data_flat059_original]
def block026_data_flat061 : CoefficientMerge.Poly := [(nat_lit 4847, Int.ofNat (nat_lit 137822544921600))]
theorem block026_data_flat061_step : block026_data_flat061 = (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) := by decide +kernel
theorem block026_data_flat061_original : block026_data_flat061 = (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) := by
  rw [block026_data_flat061_step]
def block026_data_flat062 : CoefficientMerge.Poly := [(nat_lit 4858, Int.ofNat (nat_lit 5326574012496))]
theorem block026_data_flat062_step : block026_data_flat062 = (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) := by decide +kernel
theorem block026_data_flat062_original : block026_data_flat062 = (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) := by
  rw [block026_data_flat062_step]
def block026_data_flat063 : CoefficientMerge.Poly := [(nat_lit 4859, Int.ofNat (nat_lit 2124375690096))]
theorem block026_data_flat063_step : block026_data_flat063 = (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded) := by decide +kernel
theorem block026_data_flat063_original : block026_data_flat063 = (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded) := by
  rw [block026_data_flat063_step]
def block026_data_flat064 : CoefficientMerge.Poly := [(nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096))]
theorem block026_data_flat064_step : block026_data_flat064 = (CoefficientMerge.fastMerge block026_data_flat062 block026_data_flat063) := by decide +kernel
theorem block026_data_flat064_original : block026_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)) := by
  rw [block026_data_flat064_step, block026_data_flat062_original, block026_data_flat063_original]
def block026_data_flat065 : CoefficientMerge.Poly := [(nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096))]
theorem block026_data_flat065_step : block026_data_flat065 = (CoefficientMerge.fastMerge block026_data_flat061 block026_data_flat064) := by decide +kernel
theorem block026_data_flat065_original : block026_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded))) := by
  rw [block026_data_flat065_step, block026_data_flat061_original, block026_data_flat064_original]
def block026_data_flat066 : CoefficientMerge.Poly := [(nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096))]
theorem block026_data_flat066_step : block026_data_flat066 = (CoefficientMerge.fastMerge block026_data_flat060 block026_data_flat065) := by decide +kernel
theorem block026_data_flat066_original : block026_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) := by
  rw [block026_data_flat066_step, block026_data_flat060_original, block026_data_flat065_original]
def block026_data_flat067 : CoefficientMerge.Poly := [(nat_lit 4860, Int.ofNat (nat_lit 1103782947696))]
theorem block026_data_flat067_step : block026_data_flat067 = (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) := by decide +kernel
theorem block026_data_flat067_original : block026_data_flat067 = (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) := by
  rw [block026_data_flat067_step]
def block026_data_flat068 : CoefficientMerge.Poly := [(nat_lit 4861, Int.ofNat (nat_lit 6249271357296))]
theorem block026_data_flat068_step : block026_data_flat068 = (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded) := by decide +kernel
theorem block026_data_flat068_original : block026_data_flat068 = (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded) := by
  rw [block026_data_flat068_step]
def block026_data_flat069 : CoefficientMerge.Poly := [(nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296))]
theorem block026_data_flat069_step : block026_data_flat069 = (CoefficientMerge.fastMerge block026_data_flat067 block026_data_flat068) := by decide +kernel
theorem block026_data_flat069_original : block026_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) := by
  rw [block026_data_flat069_step, block026_data_flat067_original, block026_data_flat068_original]
def block026_data_flat070 : CoefficientMerge.Poly := [(nat_lit 4862, Int.ofNat (nat_lit 11394759766896))]
theorem block026_data_flat070_step : block026_data_flat070 = (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) := by decide +kernel
theorem block026_data_flat070_original : block026_data_flat070 = (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) := by
  rw [block026_data_flat070_step]
def block026_data_flat071 : CoefficientMerge.Poly := [(nat_lit 4863, Int.ofNat (nat_lit 16540248176496))]
theorem block026_data_flat071_step : block026_data_flat071 = (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) := by decide +kernel
theorem block026_data_flat071_original : block026_data_flat071 = (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) := by
  rw [block026_data_flat071_step]
def block026_data_flat072 : CoefficientMerge.Poly := [(nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat072_step : block026_data_flat072 = (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded) := by decide +kernel
theorem block026_data_flat072_original : block026_data_flat072 = (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded) := by
  rw [block026_data_flat072_step]
def block026_data_flat073 : CoefficientMerge.Poly := [(nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat073_step : block026_data_flat073 = (CoefficientMerge.fastMerge block026_data_flat071 block026_data_flat072) := by decide +kernel
theorem block026_data_flat073_original : block026_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded)) := by
  rw [block026_data_flat073_step, block026_data_flat071_original, block026_data_flat072_original]
def block026_data_flat074 : CoefficientMerge.Poly := [(nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat074_step : block026_data_flat074 = (CoefficientMerge.fastMerge block026_data_flat070 block026_data_flat073) := by decide +kernel
theorem block026_data_flat074_original : block026_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))) := by
  rw [block026_data_flat074_step, block026_data_flat070_original, block026_data_flat073_original]
def block026_data_flat075 : CoefficientMerge.Poly := [(nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat075_step : block026_data_flat075 = (CoefficientMerge.fastMerge block026_data_flat069 block026_data_flat074) := by decide +kernel
theorem block026_data_flat075_original : block026_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded)))) := by
  rw [block026_data_flat075_step, block026_data_flat069_original, block026_data_flat074_original]
def block026_data_flat076 : CoefficientMerge.Poly := [(nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat076_step : block026_data_flat076 = (CoefficientMerge.fastMerge block026_data_flat066 block026_data_flat075) := by decide +kernel
theorem block026_data_flat076_original : block026_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))) := by
  rw [block026_data_flat076_step, block026_data_flat066_original, block026_data_flat075_original]
def block026_data_flat077 : CoefficientMerge.Poly := [(nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400)), (nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat077_step : block026_data_flat077 = (CoefficientMerge.fastMerge block026_data_flat057 block026_data_flat076) := by decide +kernel
theorem block026_data_flat077_original : block026_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded)))))) := by
  rw [block026_data_flat077_step, block026_data_flat057_original, block026_data_flat076_original]
def block026_data_flat078 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200)), (nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800)), (nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400)), (nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096))]
theorem block026_data_flat078_step : block026_data_flat078 = (CoefficientMerge.fastMerge block026_data_flat038 block026_data_flat077) := by decide +kernel
theorem block026_data_flat078_original : block026_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))))) := by
  rw [block026_data_flat078_step, block026_data_flat038_original, block026_data_flat077_original]
def block026_data_flat079 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696))]
theorem block026_data_flat079_step : block026_data_flat079 = (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) := by decide +kernel
theorem block026_data_flat079_original : block026_data_flat079 = (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) := by
  rw [block026_data_flat079_step]
def block026_data_flat080 : CoefficientMerge.Poly := [(nat_lit 4866, Int.ofNat (nat_lit 249966120888))]
theorem block026_data_flat080_step : block026_data_flat080 = (CoefficientMerge.scale (249966120888 : Int) atom1930Coded) := by decide +kernel
theorem block026_data_flat080_original : block026_data_flat080 = (CoefficientMerge.scale (249966120888 : Int) atom1930Coded) := by
  rw [block026_data_flat080_step]
def block026_data_flat081 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888))]
theorem block026_data_flat081_step : block026_data_flat081 = (CoefficientMerge.fastMerge block026_data_flat079 block026_data_flat080) := by decide +kernel
theorem block026_data_flat081_original : block026_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) := by
  rw [block026_data_flat081_step, block026_data_flat079_original, block026_data_flat080_original]
def block026_data_flat082 : CoefficientMerge.Poly := [(nat_lit 4869, Int.ofNat (nat_lit 81191673285228))]
theorem block026_data_flat082_step : block026_data_flat082 = (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) := by decide +kernel
theorem block026_data_flat082_original : block026_data_flat082 = (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) := by
  rw [block026_data_flat082_step]
def block026_data_flat083 : CoefficientMerge.Poly := [(nat_lit 4870, Int.ofNat (nat_lit 162633312691344))]
theorem block026_data_flat083_step : block026_data_flat083 = (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) := by decide +kernel
theorem block026_data_flat083_original : block026_data_flat083 = (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) := by
  rw [block026_data_flat083_step]
def block026_data_flat084 : CoefficientMerge.Poly := [(nat_lit 4871, Int.ofNat (nat_lit 258589462107042))]
theorem block026_data_flat084_step : block026_data_flat084 = (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded) := by decide +kernel
theorem block026_data_flat084_original : block026_data_flat084 = (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded) := by
  rw [block026_data_flat084_step]
def block026_data_flat085 : CoefficientMerge.Poly := [(nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042))]
theorem block026_data_flat085_step : block026_data_flat085 = (CoefficientMerge.fastMerge block026_data_flat083 block026_data_flat084) := by decide +kernel
theorem block026_data_flat085_original : block026_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)) := by
  rw [block026_data_flat085_step, block026_data_flat083_original, block026_data_flat084_original]
def block026_data_flat086 : CoefficientMerge.Poly := [(nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042))]
theorem block026_data_flat086_step : block026_data_flat086 = (CoefficientMerge.fastMerge block026_data_flat082 block026_data_flat085) := by decide +kernel
theorem block026_data_flat086_original : block026_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded))) := by
  rw [block026_data_flat086_step, block026_data_flat082_original, block026_data_flat085_original]
def block026_data_flat087 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042))]
theorem block026_data_flat087_step : block026_data_flat087 = (CoefficientMerge.fastMerge block026_data_flat081 block026_data_flat086) := by decide +kernel
theorem block026_data_flat087_original : block026_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) := by
  rw [block026_data_flat087_step, block026_data_flat081_original, block026_data_flat086_original]
def block026_data_flat088 : CoefficientMerge.Poly := [(nat_lit 4883, Int.ofNat (nat_lit 25565759604000))]
theorem block026_data_flat088_step : block026_data_flat088 = (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) := by decide +kernel
theorem block026_data_flat088_original : block026_data_flat088 = (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) := by
  rw [block026_data_flat088_step]
def block026_data_flat089 : CoefficientMerge.Poly := [(nat_lit 4884, Int.ofNat (nat_lit 31374810482400))]
theorem block026_data_flat089_step : block026_data_flat089 = (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded) := by decide +kernel
theorem block026_data_flat089_original : block026_data_flat089 = (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded) := by
  rw [block026_data_flat089_step]
def block026_data_flat090 : CoefficientMerge.Poly := [(nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400))]
theorem block026_data_flat090_step : block026_data_flat090 = (CoefficientMerge.fastMerge block026_data_flat088 block026_data_flat089) := by decide +kernel
theorem block026_data_flat090_original : block026_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) := by
  rw [block026_data_flat090_step, block026_data_flat088_original, block026_data_flat089_original]
def block026_data_flat091 : CoefficientMerge.Poly := [(nat_lit 4885, Int.ofNat (nat_lit 34479113407200))]
theorem block026_data_flat091_step : block026_data_flat091 = (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) := by decide +kernel
theorem block026_data_flat091_original : block026_data_flat091 = (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) := by
  rw [block026_data_flat091_step]
def block026_data_flat092 : CoefficientMerge.Poly := [(nat_lit 4886, Int.ofNat (nat_lit 37583416332000))]
theorem block026_data_flat092_step : block026_data_flat092 = (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) := by decide +kernel
theorem block026_data_flat092_original : block026_data_flat092 = (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) := by
  rw [block026_data_flat092_step]
def block026_data_flat093 : CoefficientMerge.Poly := [(nat_lit 4887, Int.ofNat (nat_lit 40687719256800))]
theorem block026_data_flat093_step : block026_data_flat093 = (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded) := by decide +kernel
theorem block026_data_flat093_original : block026_data_flat093 = (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded) := by
  rw [block026_data_flat093_step]
def block026_data_flat094 : CoefficientMerge.Poly := [(nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800))]
theorem block026_data_flat094_step : block026_data_flat094 = (CoefficientMerge.fastMerge block026_data_flat092 block026_data_flat093) := by decide +kernel
theorem block026_data_flat094_original : block026_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded)) := by
  rw [block026_data_flat094_step, block026_data_flat092_original, block026_data_flat093_original]
def block026_data_flat095 : CoefficientMerge.Poly := [(nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800))]
theorem block026_data_flat095_step : block026_data_flat095 = (CoefficientMerge.fastMerge block026_data_flat091 block026_data_flat094) := by decide +kernel
theorem block026_data_flat095_original : block026_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))) := by
  rw [block026_data_flat095_step, block026_data_flat091_original, block026_data_flat094_original]
def block026_data_flat096 : CoefficientMerge.Poly := [(nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800))]
theorem block026_data_flat096_step : block026_data_flat096 = (CoefficientMerge.fastMerge block026_data_flat090 block026_data_flat095) := by decide +kernel
theorem block026_data_flat096_original : block026_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded)))) := by
  rw [block026_data_flat096_step, block026_data_flat090_original, block026_data_flat095_original]
def block026_data_flat097 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800))]
theorem block026_data_flat097_step : block026_data_flat097 = (CoefficientMerge.fastMerge block026_data_flat087 block026_data_flat096) := by decide +kernel
theorem block026_data_flat097_original : block026_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) := by
  rw [block026_data_flat097_step, block026_data_flat087_original, block026_data_flat096_original]
def block026_data_flat098 : CoefficientMerge.Poly := [(nat_lit 4888, Int.ofNat (nat_lit 46875062757600))]
theorem block026_data_flat098_step : block026_data_flat098 = (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) := by decide +kernel
theorem block026_data_flat098_original : block026_data_flat098 = (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) := by
  rw [block026_data_flat098_step]
def block026_data_flat099 : CoefficientMerge.Poly := [(nat_lit 4889, Int.ofNat (nat_lit 53062406258400))]
theorem block026_data_flat099_step : block026_data_flat099 = (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded) := by decide +kernel
theorem block026_data_flat099_original : block026_data_flat099 = (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded) := by
  rw [block026_data_flat099_step]
def block026_data_flat100 : CoefficientMerge.Poly := [(nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400))]
theorem block026_data_flat100_step : block026_data_flat100 = (CoefficientMerge.fastMerge block026_data_flat098 block026_data_flat099) := by decide +kernel
theorem block026_data_flat100_original : block026_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) := by
  rw [block026_data_flat100_step, block026_data_flat098_original, block026_data_flat099_original]
def block026_data_flat101 : CoefficientMerge.Poly := [(nat_lit 4890, Int.ofNat (nat_lit 43596916084656))]
theorem block026_data_flat101_step : block026_data_flat101 = (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) := by decide +kernel
theorem block026_data_flat101_original : block026_data_flat101 = (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) := by
  rw [block026_data_flat101_step]
def block026_data_flat102 : CoefficientMerge.Poly := [(nat_lit 4891, Int.ofNat (nat_lit 40466097239040))]
theorem block026_data_flat102_step : block026_data_flat102 = (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) := by decide +kernel
theorem block026_data_flat102_original : block026_data_flat102 = (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) := by
  rw [block026_data_flat102_step]
def block026_data_flat103 : CoefficientMerge.Poly := [(nat_lit 4892, Int.ofNat (nat_lit 59252072164560))]
theorem block026_data_flat103_step : block026_data_flat103 = (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded) := by decide +kernel
theorem block026_data_flat103_original : block026_data_flat103 = (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded) := by
  rw [block026_data_flat103_step]
def block026_data_flat104 : CoefficientMerge.Poly := [(nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560))]
theorem block026_data_flat104_step : block026_data_flat104 = (CoefficientMerge.fastMerge block026_data_flat102 block026_data_flat103) := by decide +kernel
theorem block026_data_flat104_original : block026_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)) := by
  rw [block026_data_flat104_step, block026_data_flat102_original, block026_data_flat103_original]
def block026_data_flat105 : CoefficientMerge.Poly := [(nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560))]
theorem block026_data_flat105_step : block026_data_flat105 = (CoefficientMerge.fastMerge block026_data_flat101 block026_data_flat104) := by decide +kernel
theorem block026_data_flat105_original : block026_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded))) := by
  rw [block026_data_flat105_step, block026_data_flat101_original, block026_data_flat104_original]
def block026_data_flat106 : CoefficientMerge.Poly := [(nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560))]
theorem block026_data_flat106_step : block026_data_flat106 = (CoefficientMerge.fastMerge block026_data_flat100 block026_data_flat105) := by decide +kernel
theorem block026_data_flat106_original : block026_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) := by
  rw [block026_data_flat106_step, block026_data_flat100_original, block026_data_flat105_original]
def block026_data_flat107 : CoefficientMerge.Poly := [(nat_lit 4893, Int.ofNat (nat_lit 145083165594840))]
theorem block026_data_flat107_step : block026_data_flat107 = (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) := by decide +kernel
theorem block026_data_flat107_original : block026_data_flat107 = (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) := by
  rw [block026_data_flat107_step]
def block026_data_flat108 : CoefficientMerge.Poly := [(nat_lit 4894, Int.ofNat (nat_lit 241202304677664))]
theorem block026_data_flat108_step : block026_data_flat108 = (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded) := by decide +kernel
theorem block026_data_flat108_original : block026_data_flat108 = (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded) := by
  rw [block026_data_flat108_step]
def block026_data_flat109 : CoefficientMerge.Poly := [(nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664))]
theorem block026_data_flat109_step : block026_data_flat109 = (CoefficientMerge.fastMerge block026_data_flat107 block026_data_flat108) := by decide +kernel
theorem block026_data_flat109_original : block026_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) := by
  rw [block026_data_flat109_step, block026_data_flat107_original, block026_data_flat108_original]
def block026_data_flat110 : CoefficientMerge.Poly := [(nat_lit 4895, Int.ofNat (nat_lit 351539881100100))]
theorem block026_data_flat110_step : block026_data_flat110 = (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) := by decide +kernel
theorem block026_data_flat110_original : block026_data_flat110 = (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) := by
  rw [block026_data_flat110_step]
def block026_data_flat111 : CoefficientMerge.Poly := [(nat_lit 4908, Int.ofNat (nat_lit 34577008804800))]
theorem block026_data_flat111_step : block026_data_flat111 = (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) := by decide +kernel
theorem block026_data_flat111_original : block026_data_flat111 = (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) := by
  rw [block026_data_flat111_step]
def block026_data_flat112 : CoefficientMerge.Poly := [(nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat112_step : block026_data_flat112 = (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded) := by decide +kernel
theorem block026_data_flat112_original : block026_data_flat112 = (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded) := by
  rw [block026_data_flat112_step]
def block026_data_flat113 : CoefficientMerge.Poly := [(nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat113_step : block026_data_flat113 = (CoefficientMerge.fastMerge block026_data_flat111 block026_data_flat112) := by decide +kernel
theorem block026_data_flat113_original : block026_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)) := by
  rw [block026_data_flat113_step, block026_data_flat111_original, block026_data_flat112_original]
def block026_data_flat114 : CoefficientMerge.Poly := [(nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat114_step : block026_data_flat114 = (CoefficientMerge.fastMerge block026_data_flat110 block026_data_flat113) := by decide +kernel
theorem block026_data_flat114_original : block026_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded))) := by
  rw [block026_data_flat114_step, block026_data_flat110_original, block026_data_flat113_original]
def block026_data_flat115 : CoefficientMerge.Poly := [(nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat115_step : block026_data_flat115 = (CoefficientMerge.fastMerge block026_data_flat109 block026_data_flat114) := by decide +kernel
theorem block026_data_flat115_original : block026_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))) := by
  rw [block026_data_flat115_step, block026_data_flat109_original, block026_data_flat114_original]
def block026_data_flat116 : CoefficientMerge.Poly := [(nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat116_step : block026_data_flat116 = (CoefficientMerge.fastMerge block026_data_flat106 block026_data_flat115) := by decide +kernel
theorem block026_data_flat116_original : block026_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded))))) := by
  rw [block026_data_flat116_step, block026_data_flat106_original, block026_data_flat115_original]
def block026_data_flat117 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800)), (nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200))]
theorem block026_data_flat117_step : block026_data_flat117 = (CoefficientMerge.fastMerge block026_data_flat097 block026_data_flat116) := by decide +kernel
theorem block026_data_flat117_original : block026_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) := by
  rw [block026_data_flat117_step, block026_data_flat097_original, block026_data_flat116_original]
def block026_data_flat118 : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 69757336756800))]
theorem block026_data_flat118_step : block026_data_flat118 = (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) := by decide +kernel
theorem block026_data_flat118_original : block026_data_flat118 = (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) := by
  rw [block026_data_flat118_step]
def block026_data_flat119 : CoefficientMerge.Poly := [(nat_lit 4911, Int.ofNat (nat_lit 75965942606400))]
theorem block026_data_flat119_step : block026_data_flat119 = (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded) := by decide +kernel
theorem block026_data_flat119_original : block026_data_flat119 = (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded) := by
  rw [block026_data_flat119_step]
def block026_data_flat120 : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400))]
theorem block026_data_flat120_step : block026_data_flat120 = (CoefficientMerge.fastMerge block026_data_flat118 block026_data_flat119) := by decide +kernel
theorem block026_data_flat120_original : block026_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) := by
  rw [block026_data_flat120_step, block026_data_flat118_original, block026_data_flat119_original]
def block026_data_flat121 : CoefficientMerge.Poly := [(nat_lit 4912, Int.ofNat (nat_lit 82174548456000))]
theorem block026_data_flat121_step : block026_data_flat121 = (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) := by decide +kernel
theorem block026_data_flat121_original : block026_data_flat121 = (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) := by
  rw [block026_data_flat121_step]
def block026_data_flat122 : CoefficientMerge.Poly := [(nat_lit 4913, Int.ofNat (nat_lit 88383154305600))]
theorem block026_data_flat122_step : block026_data_flat122 = (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) := by decide +kernel
theorem block026_data_flat122_original : block026_data_flat122 = (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) := by
  rw [block026_data_flat122_step]
def block026_data_flat123 : CoefficientMerge.Poly := [(nat_lit 4914, Int.ofNat (nat_lit 124602611211936))]
theorem block026_data_flat123_step : block026_data_flat123 = (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded) := by decide +kernel
theorem block026_data_flat123_original : block026_data_flat123 = (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded) := by
  rw [block026_data_flat123_step]
def block026_data_flat124 : CoefficientMerge.Poly := [(nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936))]
theorem block026_data_flat124_step : block026_data_flat124 = (CoefficientMerge.fastMerge block026_data_flat122 block026_data_flat123) := by decide +kernel
theorem block026_data_flat124_original : block026_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)) := by
  rw [block026_data_flat124_step, block026_data_flat122_original, block026_data_flat123_original]
def block026_data_flat125 : CoefficientMerge.Poly := [(nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936))]
theorem block026_data_flat125_step : block026_data_flat125 = (CoefficientMerge.fastMerge block026_data_flat121 block026_data_flat124) := by decide +kernel
theorem block026_data_flat125_original : block026_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded))) := by
  rw [block026_data_flat125_step, block026_data_flat121_original, block026_data_flat124_original]
def block026_data_flat126 : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936))]
theorem block026_data_flat126_step : block026_data_flat126 = (CoefficientMerge.fastMerge block026_data_flat120 block026_data_flat125) := by decide +kernel
theorem block026_data_flat126_original : block026_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) := by
  rw [block026_data_flat126_step, block026_data_flat120_original, block026_data_flat125_original]
def block026_data_flat127 : CoefficientMerge.Poly := [(nat_lit 4915, Int.ofNat (nat_lit 106592002007040))]
theorem block026_data_flat127_step : block026_data_flat127 = (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) := by decide +kernel
theorem block026_data_flat127_original : block026_data_flat127 = (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) := by
  rw [block026_data_flat127_step]
def block026_data_flat128 : CoefficientMerge.Poly := [(nat_lit 4916, Int.ofNat (nat_lit 198627432996960))]
theorem block026_data_flat128_step : block026_data_flat128 = (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded) := by decide +kernel
theorem block026_data_flat128_original : block026_data_flat128 = (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded) := by
  rw [block026_data_flat128_step]
def block026_data_flat129 : CoefficientMerge.Poly := [(nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960))]
theorem block026_data_flat129_step : block026_data_flat129 = (CoefficientMerge.fastMerge block026_data_flat127 block026_data_flat128) := by decide +kernel
theorem block026_data_flat129_original : block026_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) := by
  rw [block026_data_flat129_step, block026_data_flat127_original, block026_data_flat128_original]
def block026_data_flat130 : CoefficientMerge.Poly := [(nat_lit 4917, Int.ofNat (nat_lit 222778113679440))]
theorem block026_data_flat130_step : block026_data_flat130 = (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) := by decide +kernel
theorem block026_data_flat130_original : block026_data_flat130 = (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) := by
  rw [block026_data_flat130_step]
def block026_data_flat131 : CoefficientMerge.Poly := [(nat_lit 4918, Int.ofNat (nat_lit 316603111771584))]
theorem block026_data_flat131_step : block026_data_flat131 = (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) := by decide +kernel
theorem block026_data_flat131_original : block026_data_flat131 = (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) := by
  rw [block026_data_flat131_step]
def block026_data_flat132 : CoefficientMerge.Poly := [(nat_lit 4919, Int.ofNat (nat_lit 419646672660600))]
theorem block026_data_flat132_step : block026_data_flat132 = (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded) := by decide +kernel
theorem block026_data_flat132_original : block026_data_flat132 = (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded) := by
  rw [block026_data_flat132_step]
def block026_data_flat133 : CoefficientMerge.Poly := [(nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600))]
theorem block026_data_flat133_step : block026_data_flat133 = (CoefficientMerge.fastMerge block026_data_flat131 block026_data_flat132) := by decide +kernel
theorem block026_data_flat133_original : block026_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded)) := by
  rw [block026_data_flat133_step, block026_data_flat131_original, block026_data_flat132_original]
def block026_data_flat134 : CoefficientMerge.Poly := [(nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600))]
theorem block026_data_flat134_step : block026_data_flat134 = (CoefficientMerge.fastMerge block026_data_flat130 block026_data_flat133) := by decide +kernel
theorem block026_data_flat134_original : block026_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))) := by
  rw [block026_data_flat134_step, block026_data_flat130_original, block026_data_flat133_original]
def block026_data_flat135 : CoefficientMerge.Poly := [(nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600))]
theorem block026_data_flat135_step : block026_data_flat135 = (CoefficientMerge.fastMerge block026_data_flat129 block026_data_flat134) := by decide +kernel
theorem block026_data_flat135_original : block026_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded)))) := by
  rw [block026_data_flat135_step, block026_data_flat129_original, block026_data_flat134_original]
def block026_data_flat136 : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600))]
theorem block026_data_flat136_step : block026_data_flat136 = (CoefficientMerge.fastMerge block026_data_flat126 block026_data_flat135) := by decide +kernel
theorem block026_data_flat136_original : block026_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) := by
  rw [block026_data_flat136_step, block026_data_flat126_original, block026_data_flat135_original]
def block026_data_flat137 : CoefficientMerge.Poly := [(nat_lit 4933, Int.ofNat (nat_lit 57739680028800))]
theorem block026_data_flat137_step : block026_data_flat137 = (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) := by decide +kernel
theorem block026_data_flat137_original : block026_data_flat137 = (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) := by
  rw [block026_data_flat137_step]
def block026_data_flat138 : CoefficientMerge.Poly := [(nat_lit 4934, Int.ofNat (nat_lit 108361788796800))]
theorem block026_data_flat138_step : block026_data_flat138 = (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded) := by decide +kernel
theorem block026_data_flat138_original : block026_data_flat138 = (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded) := by
  rw [block026_data_flat138_step]
def block026_data_flat139 : CoefficientMerge.Poly := [(nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800))]
theorem block026_data_flat139_step : block026_data_flat139 = (CoefficientMerge.fastMerge block026_data_flat137 block026_data_flat138) := by decide +kernel
theorem block026_data_flat139_original : block026_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) := by
  rw [block026_data_flat139_step, block026_data_flat137_original, block026_data_flat138_original]
def block026_data_flat140 : CoefficientMerge.Poly := [(nat_lit 4935, Int.ofNat (nat_lit 110488023676800))]
theorem block026_data_flat140_step : block026_data_flat140 = (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) := by decide +kernel
theorem block026_data_flat140_original : block026_data_flat140 = (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) := by
  rw [block026_data_flat140_step]
def block026_data_flat141 : CoefficientMerge.Poly := [(nat_lit 4936, Int.ofNat (nat_lit 115697299132800))]
theorem block026_data_flat141_step : block026_data_flat141 = (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) := by decide +kernel
theorem block026_data_flat141_original : block026_data_flat141 = (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) := by
  rw [block026_data_flat141_step]
def block026_data_flat142 : CoefficientMerge.Poly := [(nat_lit 4937, Int.ofNat (nat_lit 120906574588800))]
theorem block026_data_flat142_step : block026_data_flat142 = (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded) := by decide +kernel
theorem block026_data_flat142_original : block026_data_flat142 = (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded) := by
  rw [block026_data_flat142_step]
def block026_data_flat143 : CoefficientMerge.Poly := [(nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800))]
theorem block026_data_flat143_step : block026_data_flat143 = (CoefficientMerge.fastMerge block026_data_flat141 block026_data_flat142) := by decide +kernel
theorem block026_data_flat143_original : block026_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)) := by
  rw [block026_data_flat143_step, block026_data_flat141_original, block026_data_flat142_original]
def block026_data_flat144 : CoefficientMerge.Poly := [(nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800))]
theorem block026_data_flat144_step : block026_data_flat144 = (CoefficientMerge.fastMerge block026_data_flat140 block026_data_flat143) := by decide +kernel
theorem block026_data_flat144_original : block026_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded))) := by
  rw [block026_data_flat144_step, block026_data_flat140_original, block026_data_flat143_original]
def block026_data_flat145 : CoefficientMerge.Poly := [(nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800))]
theorem block026_data_flat145_step : block026_data_flat145 = (CoefficientMerge.fastMerge block026_data_flat139 block026_data_flat144) := by decide +kernel
theorem block026_data_flat145_original : block026_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) := by
  rw [block026_data_flat145_step, block026_data_flat139_original, block026_data_flat144_original]
def block026_data_flat146 : CoefficientMerge.Poly := [(nat_lit 4938, Int.ofNat (nat_lit 152275157496000))]
theorem block026_data_flat146_step : block026_data_flat146 = (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) := by decide +kernel
theorem block026_data_flat146_original : block026_data_flat146 = (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) := by
  rw [block026_data_flat146_step]
def block026_data_flat147 : CoefficientMerge.Poly := [(nat_lit 4939, Int.ofNat (nat_lit 142638050016000))]
theorem block026_data_flat147_step : block026_data_flat147 = (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded) := by decide +kernel
theorem block026_data_flat147_original : block026_data_flat147 = (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded) := by
  rw [block026_data_flat147_step]
def block026_data_flat148 : CoefficientMerge.Poly := [(nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000))]
theorem block026_data_flat148_step : block026_data_flat148 = (CoefficientMerge.fastMerge block026_data_flat146 block026_data_flat147) := by decide +kernel
theorem block026_data_flat148_original : block026_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) := by
  rw [block026_data_flat148_step, block026_data_flat146_original, block026_data_flat147_original]
def block026_data_flat149 : CoefficientMerge.Poly := [(nat_lit 4940, Int.ofNat (nat_lit 245003491656000))]
theorem block026_data_flat149_step : block026_data_flat149 = (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) := by decide +kernel
theorem block026_data_flat149_original : block026_data_flat149 = (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) := by
  rw [block026_data_flat149_step]
def block026_data_flat150 : CoefficientMerge.Poly := [(nat_lit 4941, Int.ofNat (nat_lit 267452024162400))]
theorem block026_data_flat150_step : block026_data_flat150 = (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) := by decide +kernel
theorem block026_data_flat150_original : block026_data_flat150 = (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) := by
  rw [block026_data_flat150_step]
def block026_data_flat151 : CoefficientMerge.Poly := [(nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat151_step : block026_data_flat151 = (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded) := by decide +kernel
theorem block026_data_flat151_original : block026_data_flat151 = (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded) := by
  rw [block026_data_flat151_step]
def block026_data_flat152 : CoefficientMerge.Poly := [(nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat152_step : block026_data_flat152 = (CoefficientMerge.fastMerge block026_data_flat150 block026_data_flat151) := by decide +kernel
theorem block026_data_flat152_original : block026_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)) := by
  rw [block026_data_flat152_step, block026_data_flat150_original, block026_data_flat151_original]
def block026_data_flat153 : CoefficientMerge.Poly := [(nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat153_step : block026_data_flat153 = (CoefficientMerge.fastMerge block026_data_flat149 block026_data_flat152) := by decide +kernel
theorem block026_data_flat153_original : block026_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded))) := by
  rw [block026_data_flat153_step, block026_data_flat149_original, block026_data_flat152_original]
def block026_data_flat154 : CoefficientMerge.Poly := [(nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat154_step : block026_data_flat154 = (CoefficientMerge.fastMerge block026_data_flat148 block026_data_flat153) := by decide +kernel
theorem block026_data_flat154_original : block026_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)))) := by
  rw [block026_data_flat154_step, block026_data_flat148_original, block026_data_flat153_original]
def block026_data_flat155 : CoefficientMerge.Poly := [(nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat155_step : block026_data_flat155 = (CoefficientMerge.fastMerge block026_data_flat145 block026_data_flat154) := by decide +kernel
theorem block026_data_flat155_original : block026_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded))))) := by
  rw [block026_data_flat155_step, block026_data_flat145_original, block026_data_flat154_original]
def block026_data_flat156 : CoefficientMerge.Poly := [(nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600)), (nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat156_step : block026_data_flat156 = (CoefficientMerge.fastMerge block026_data_flat136 block026_data_flat155) := by decide +kernel
theorem block026_data_flat156_original : block026_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)))))) := by
  rw [block026_data_flat156_step, block026_data_flat136_original, block026_data_flat155_original]
def block026_data_flat157 : CoefficientMerge.Poly := [(nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800)), (nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200)), (nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600)), (nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat157_step : block026_data_flat157 = (CoefficientMerge.fastMerge block026_data_flat117 block026_data_flat156) := by decide +kernel
theorem block026_data_flat157_original : block026_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded))))))) := by
  rw [block026_data_flat157_step, block026_data_flat117_original, block026_data_flat156_original]
def block026_data_flat158 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200)), (nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800)), (nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400)), (nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096)), (nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800)), (nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200)), (nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600)), (nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat158_step : block026_data_flat158 = (CoefficientMerge.fastMerge block026_data_flat078 block026_data_flat157) := by decide +kernel
theorem block026_data_flat158_original : block026_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)))))))) := by
  rw [block026_data_flat158_step, block026_data_flat078_original, block026_data_flat157_original]
def block026_data_flat159 : CoefficientMerge.Poly := [(nat_lit 4463, Int.ofNat (nat_lit 690781818988800)), (nat_lit 4482, Int.ofNat (nat_lit 202067913062400)), (nat_lit 4483, Int.ofNat (nat_lit 390017626521600)), (nat_lit 4484, Int.ofNat (nat_lit 587162124595200)), (nat_lit 4485, Int.ofNat (nat_lit 591060221875200)), (nat_lit 4486, Int.ofNat (nat_lit 465720930796800)), (nat_lit 4487, Int.ofNat (nat_lit 672974601868800)), (nat_lit 4507, Int.ofNat (nat_lit 129207041187840)), (nat_lit 4508, Int.ofNat (nat_lit 426796764979200)), (nat_lit 4509, Int.ofNat (nat_lit 432844721971200)), (nat_lit 4510, Int.ofNat (nat_lit 378326949996800)), (nat_lit 4511, Int.ofNat (nat_lit 440381097072000)), (nat_lit 4532, Int.ofNat (nat_lit 309267950745600)), (nat_lit 4533, Int.ofNat (nat_lit 450681470131200)), (nat_lit 4534, Int.ofNat (nat_lit 366850113996800)), (nat_lit 4535, Int.ofNat (nat_lit 455881349347200)), (nat_lit 4557, Int.ofNat (nat_lit 89500313548800)), (nat_lit 4558, Int.ofNat (nat_lit 153592979366400)), (nat_lit 4559, Int.ofNat (nat_lit 236387787048000)), (nat_lit 4808, Int.ofNat (nat_lit 15968023948800)), (nat_lit 4809, Int.ofNat (nat_lit 30188327122800)), (nat_lit 4810, Int.ofNat (nat_lit 2502889795296)), (nat_lit 4811, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4833, Int.ofNat (nat_lit 35074459173600)), (nat_lit 4834, Int.ofNat (nat_lit 17799156411696)), (nat_lit 4838, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4839, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4840, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4841, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4843, Int.ofNat (nat_lit 1197778982400)), (nat_lit 4845, Int.ofNat (nat_lit 45125791603200)), (nat_lit 4846, Int.ofNat (nat_lit 87856025241600)), (nat_lit 4847, Int.ofNat (nat_lit 137822544921600)), (nat_lit 4858, Int.ofNat (nat_lit 5326574012496)), (nat_lit 4859, Int.ofNat (nat_lit 2124375690096)), (nat_lit 4860, Int.ofNat (nat_lit 1103782947696)), (nat_lit 4861, Int.ofNat (nat_lit 6249271357296)), (nat_lit 4862, Int.ofNat (nat_lit 11394759766896)), (nat_lit 4863, Int.ofNat (nat_lit 16540248176496)), (nat_lit 4864, Int.ofNat (nat_lit 21685736586096)), (nat_lit 4865, Int.ofNat (nat_lit 26831224995696)), (nat_lit 4866, Int.ofNat (nat_lit 249966120888)), (nat_lit 4869, Int.ofNat (nat_lit 81191673285228)), (nat_lit 4870, Int.ofNat (nat_lit 162633312691344)), (nat_lit 4871, Int.ofNat (nat_lit 258589462107042)), (nat_lit 4883, Int.ofNat (nat_lit 25565759604000)), (nat_lit 4884, Int.ofNat (nat_lit 31374810482400)), (nat_lit 4885, Int.ofNat (nat_lit 34479113407200)), (nat_lit 4886, Int.ofNat (nat_lit 37583416332000)), (nat_lit 4887, Int.ofNat (nat_lit 40687719256800)), (nat_lit 4888, Int.ofNat (nat_lit 46875062757600)), (nat_lit 4889, Int.ofNat (nat_lit 53062406258400)), (nat_lit 4890, Int.ofNat (nat_lit 43596916084656)), (nat_lit 4891, Int.ofNat (nat_lit 40466097239040)), (nat_lit 4892, Int.ofNat (nat_lit 59252072164560)), (nat_lit 4893, Int.ofNat (nat_lit 145083165594840)), (nat_lit 4894, Int.ofNat (nat_lit 241202304677664)), (nat_lit 4895, Int.ofNat (nat_lit 351539881100100)), (nat_lit 4908, Int.ofNat (nat_lit 34577008804800)), (nat_lit 4909, Int.ofNat (nat_lit 63548730907200)), (nat_lit 4910, Int.ofNat (nat_lit 69757336756800)), (nat_lit 4911, Int.ofNat (nat_lit 75965942606400)), (nat_lit 4912, Int.ofNat (nat_lit 82174548456000)), (nat_lit 4913, Int.ofNat (nat_lit 88383154305600)), (nat_lit 4914, Int.ofNat (nat_lit 124602611211936)), (nat_lit 4915, Int.ofNat (nat_lit 106592002007040)), (nat_lit 4916, Int.ofNat (nat_lit 198627432996960)), (nat_lit 4917, Int.ofNat (nat_lit 222778113679440)), (nat_lit 4918, Int.ofNat (nat_lit 316603111771584)), (nat_lit 4919, Int.ofNat (nat_lit 419646672660600)), (nat_lit 4933, Int.ofNat (nat_lit 57739680028800)), (nat_lit 4934, Int.ofNat (nat_lit 108361788796800)), (nat_lit 4935, Int.ofNat (nat_lit 110488023676800)), (nat_lit 4936, Int.ofNat (nat_lit 115697299132800)), (nat_lit 4937, Int.ofNat (nat_lit 120906574588800)), (nat_lit 4938, Int.ofNat (nat_lit 152275157496000)), (nat_lit 4939, Int.ofNat (nat_lit 142638050016000)), (nat_lit 4940, Int.ofNat (nat_lit 245003491656000)), (nat_lit 4941, Int.ofNat (nat_lit 267452024162400)), (nat_lit 4942, Int.ofNat (nat_lit 367278829948800))]
theorem block026_data_flat159_step : block026_data_flat159 = (CoefficientMerge.trim block026_data_flat158) := by decide +kernel
theorem block026_data_flat159_original : block026_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded))))))))) := by
  rw [block026_data_flat159_step, block026_data_flat158_original]
theorem block026_data : block026 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690781818988800 : Int) atom1889Coded) (CoefficientMerge.scale (202067913062400 : Int) atom1890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390017626521600 : Int) atom1891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587162124595200 : Int) atom1892Coded) (CoefficientMerge.scale (591060221875200 : Int) atom1893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (465720930796800 : Int) atom1894Coded) (CoefficientMerge.scale (672974601868800 : Int) atom1895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129207041187840 : Int) atom1896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (426796764979200 : Int) atom1897Coded) (CoefficientMerge.scale (432844721971200 : Int) atom1898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (378326949996800 : Int) atom1899Coded) (CoefficientMerge.scale (440381097072000 : Int) atom1900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309267950745600 : Int) atom1901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450681470131200 : Int) atom1902Coded) (CoefficientMerge.scale (366850113996800 : Int) atom1903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (455881349347200 : Int) atom1904Coded) (CoefficientMerge.scale (89500313548800 : Int) atom1905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153592979366400 : Int) atom1906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (236387787048000 : Int) atom1907Coded) (CoefficientMerge.scale (15968023948800 : Int) atom1908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30188327122800 : Int) atom1909Coded) (CoefficientMerge.scale (2502889795296 : Int) atom1910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35074459173600 : Int) atom1912Coded) (CoefficientMerge.scale (17799156411696 : Int) atom1913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1914Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1917Coded) (CoefficientMerge.scale (1197778982400 : Int) atom1918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom1919Coded) (CoefficientMerge.scale (87856025241600 : Int) atom1920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom1921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5326574012496 : Int) atom1922Coded) (CoefficientMerge.scale (2124375690096 : Int) atom1923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1103782947696 : Int) atom1924Coded) (CoefficientMerge.scale (6249271357296 : Int) atom1925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11394759766896 : Int) atom1926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16540248176496 : Int) atom1927Coded) (CoefficientMerge.scale (21685736586096 : Int) atom1928Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26831224995696 : Int) atom1929Coded) (CoefficientMerge.scale (249966120888 : Int) atom1930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81191673285228 : Int) atom1931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162633312691344 : Int) atom1932Coded) (CoefficientMerge.scale (258589462107042 : Int) atom1933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25565759604000 : Int) atom1934Coded) (CoefficientMerge.scale (31374810482400 : Int) atom1935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34479113407200 : Int) atom1936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37583416332000 : Int) atom1937Coded) (CoefficientMerge.scale (40687719256800 : Int) atom1938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46875062757600 : Int) atom1939Coded) (CoefficientMerge.scale (53062406258400 : Int) atom1940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43596916084656 : Int) atom1941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40466097239040 : Int) atom1942Coded) (CoefficientMerge.scale (59252072164560 : Int) atom1943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (145083165594840 : Int) atom1944Coded) (CoefficientMerge.scale (241202304677664 : Int) atom1945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351539881100100 : Int) atom1946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34577008804800 : Int) atom1947Coded) (CoefficientMerge.scale (63548730907200 : Int) atom1948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69757336756800 : Int) atom1949Coded) (CoefficientMerge.scale (75965942606400 : Int) atom1950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82174548456000 : Int) atom1951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88383154305600 : Int) atom1952Coded) (CoefficientMerge.scale (124602611211936 : Int) atom1953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (106592002007040 : Int) atom1954Coded) (CoefficientMerge.scale (198627432996960 : Int) atom1955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (222778113679440 : Int) atom1956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (316603111771584 : Int) atom1957Coded) (CoefficientMerge.scale (419646672660600 : Int) atom1958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57739680028800 : Int) atom1959Coded) (CoefficientMerge.scale (108361788796800 : Int) atom1960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110488023676800 : Int) atom1961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115697299132800 : Int) atom1962Coded) (CoefficientMerge.scale (120906574588800 : Int) atom1963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152275157496000 : Int) atom1964Coded) (CoefficientMerge.scale (142638050016000 : Int) atom1965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245003491656000 : Int) atom1966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (267452024162400 : Int) atom1967Coded) (CoefficientMerge.scale (367278829948800 : Int) atom1968Coded)))))))) := by
  have h : block026 = block026_data_flat159 := by decide +kernel
  exact h.trans block026_data_flat159_original
theorem block026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block026 := by
  rw [block026_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1889Coded_nonneg g hg hA hB) (atom1890Coded_nonneg g hg hA hB)) (add_nonneg (atom1891Coded_nonneg g hg hA hB) (add_nonneg (atom1892Coded_nonneg g hg hA hB) (atom1893Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1894Coded_nonneg g hg hA hB) (atom1895Coded_nonneg g hg hA hB)) (add_nonneg (atom1896Coded_nonneg g hg hA hB) (add_nonneg (atom1897Coded_nonneg g hg hA hB) (atom1898Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1899Coded_nonneg g hg hA hB) (atom1900Coded_nonneg g hg hA hB)) (add_nonneg (atom1901Coded_nonneg g hg hA hB) (add_nonneg (atom1902Coded_nonneg g hg hA hB) (atom1903Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1904Coded_nonneg g hg hA hB) (atom1905Coded_nonneg g hg hA hB)) (add_nonneg (atom1906Coded_nonneg g hg hA hB) (add_nonneg (atom1907Coded_nonneg g hg hA hB) (atom1908Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1909Coded_nonneg g hg hA hB) (atom1910Coded_nonneg g hg hA hB)) (add_nonneg (atom1911Coded_nonneg g hg hA hB) (add_nonneg (atom1912Coded_nonneg g hg hA hB) (atom1913Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1914Coded_nonneg g hg hA hB) (atom1915Coded_nonneg g hg hA hB)) (add_nonneg (atom1916Coded_nonneg g hg hA hB) (add_nonneg (atom1917Coded_nonneg g hg hA hB) (atom1918Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1919Coded_nonneg g hg hA hB) (atom1920Coded_nonneg g hg hA hB)) (add_nonneg (atom1921Coded_nonneg g hg hA hB) (add_nonneg (atom1922Coded_nonneg g hg hA hB) (atom1923Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1924Coded_nonneg g hg hA hB) (atom1925Coded_nonneg g hg hA hB)) (add_nonneg (atom1926Coded_nonneg g hg hA hB) (add_nonneg (atom1927Coded_nonneg g hg hA hB) (atom1928Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1929Coded_nonneg g hg hA hB) (atom1930Coded_nonneg g hg hA hB)) (add_nonneg (atom1931Coded_nonneg g hg hA hB) (add_nonneg (atom1932Coded_nonneg g hg hA hB) (atom1933Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1934Coded_nonneg g hg hA hB) (atom1935Coded_nonneg g hg hA hB)) (add_nonneg (atom1936Coded_nonneg g hg hA hB) (add_nonneg (atom1937Coded_nonneg g hg hA hB) (atom1938Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1939Coded_nonneg g hg hA hB) (atom1940Coded_nonneg g hg hA hB)) (add_nonneg (atom1941Coded_nonneg g hg hA hB) (add_nonneg (atom1942Coded_nonneg g hg hA hB) (atom1943Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1944Coded_nonneg g hg hA hB) (atom1945Coded_nonneg g hg hA hB)) (add_nonneg (atom1946Coded_nonneg g hg hA hB) (add_nonneg (atom1947Coded_nonneg g hg hA hB) (atom1948Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1949Coded_nonneg g hg hA hB) (atom1950Coded_nonneg g hg hA hB)) (add_nonneg (atom1951Coded_nonneg g hg hA hB) (add_nonneg (atom1952Coded_nonneg g hg hA hB) (atom1953Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1954Coded_nonneg g hg hA hB) (atom1955Coded_nonneg g hg hA hB)) (add_nonneg (atom1956Coded_nonneg g hg hA hB) (add_nonneg (atom1957Coded_nonneg g hg hA hB) (atom1958Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1959Coded_nonneg g hg hA hB) (atom1960Coded_nonneg g hg hA hB)) (add_nonneg (atom1961Coded_nonneg g hg hA hB) (add_nonneg (atom1962Coded_nonneg g hg hA hB) (atom1963Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1964Coded_nonneg g hg hA hB) (atom1965Coded_nonneg g hg hA hB)) (add_nonneg (atom1966Coded_nonneg g hg hA hB) (add_nonneg (atom1967Coded_nonneg g hg hA hB) (atom1968Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
