import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1969 : SparsePolynomial.Poly := [([8,13,23], 1)]
theorem eval_atom1969 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1969 = ((g 8) * (g 13) * (g 23)) := by
  norm_num [atom1969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1969_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (476282593155600 : Int) atom1969) := by
  rw [SparsePolynomial.eval_scale, eval_atom1969]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1969Coded : CoefficientMerge.Poly := [(4943, 1)]
theorem atom1969Coded_decode : atom1969 = SparsePolynomial.decodeCubic 24 atom1969Coded := by decide +kernel
theorem atom1969Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (476282593155600 : Int) atom1969Coded) := by
  have h := atom1969_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1969Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1970 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom1970 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1970 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom1970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1970_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79390066694400 : Int) atom1970) := by
  rw [SparsePolynomial.eval_scale, eval_atom1970]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1970Coded : CoefficientMerge.Poly := [(4958, 1)]
theorem atom1970Coded_decode : atom1970 = SparsePolynomial.decodeCubic 24 atom1970Coded := by decide +kernel
theorem atom1970Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79390066694400 : Int) atom1970Coded) := by
  have h := atom1970_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1970Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1971 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom1971 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1971 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom1971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1971_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153751587897600 : Int) atom1971) := by
  rw [SparsePolynomial.eval_scale, eval_atom1971]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1971Coded : CoefficientMerge.Poly := [(4959, 1)]
theorem atom1971Coded_decode : atom1971 = SparsePolynomial.decodeCubic 24 atom1971Coded := by decide +kernel
theorem atom1971Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153751587897600 : Int) atom1971Coded) := by
  have h := atom1971_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1971Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1972 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom1972 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1972 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom1972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1972_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156940940217600 : Int) atom1972) := by
  rw [SparsePolynomial.eval_scale, eval_atom1972]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1972Coded : CoefficientMerge.Poly := [(4960, 1)]
theorem atom1972Coded_decode : atom1972 = SparsePolynomial.decodeCubic 24 atom1972Coded := by decide +kernel
theorem atom1972Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156940940217600 : Int) atom1972Coded) := by
  have h := atom1972_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1972Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1973 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom1973 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1973 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom1973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1973_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (160130292537600 : Int) atom1973) := by
  rw [SparsePolynomial.eval_scale, eval_atom1973]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1973Coded : CoefficientMerge.Poly := [(4961, 1)]
theorem atom1973Coded_decode : atom1973 = SparsePolynomial.decodeCubic 24 atom1973Coded := by decide +kernel
theorem atom1973Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (160130292537600 : Int) atom1973Coded) := by
  have h := atom1973_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1973Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1974 : SparsePolynomial.Poly := [([8,14,18], 1)]
theorem eval_atom1974 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1974 = ((g 8) * (g 14) * (g 18)) := by
  norm_num [atom1974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1974_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174436309555200 : Int) atom1974) := by
  rw [SparsePolynomial.eval_scale, eval_atom1974]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1974Coded : CoefficientMerge.Poly := [(4962, 1)]
theorem atom1974Coded_decode : atom1974 = SparsePolynomial.decodeCubic 24 atom1974Coded := by decide +kernel
theorem atom1974Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (174436309555200 : Int) atom1974Coded) := by
  have h := atom1974_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1974Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1975 : SparsePolynomial.Poly := [([8,14,19], 1)]
theorem eval_atom1975 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1975 = ((g 8) * (g 14) * (g 19)) := by
  norm_num [atom1975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1975_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177035188730400 : Int) atom1975) := by
  rw [SparsePolynomial.eval_scale, eval_atom1975]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1975Coded : CoefficientMerge.Poly := [(4963, 1)]
theorem atom1975Coded_decode : atom1975 = SparsePolynomial.decodeCubic 24 atom1975Coded := by decide +kernel
theorem atom1975Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177035188730400 : Int) atom1975Coded) := by
  have h := atom1975_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1975Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1976 : SparsePolynomial.Poly := [([8,14,20], 1)]
theorem eval_atom1976 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1976 = ((g 8) * (g 14) * (g 20)) := by
  norm_num [atom1976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1976_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282193893273600 : Int) atom1976) := by
  rw [SparsePolynomial.eval_scale, eval_atom1976]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1976Coded : CoefficientMerge.Poly := [(4964, 1)]
theorem atom1976Coded_decode : atom1976 = SparsePolynomial.decodeCubic 24 atom1976Coded := by decide +kernel
theorem atom1976Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (282193893273600 : Int) atom1976Coded) := by
  have h := atom1976_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1976Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1977 : SparsePolynomial.Poly := [([8,14,21], 1)]
theorem eval_atom1977 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1977 = ((g 8) * (g 14) * (g 21)) := by
  norm_num [atom1977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1977_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312992405510400 : Int) atom1977) := by
  rw [SparsePolynomial.eval_scale, eval_atom1977]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1977Coded : CoefficientMerge.Poly := [(4965, 1)]
theorem atom1977Coded_decode : atom1977 = SparsePolynomial.decodeCubic 24 atom1977Coded := by decide +kernel
theorem atom1977Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (312992405510400 : Int) atom1977Coded) := by
  have h := atom1977_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1977Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1978 : SparsePolynomial.Poly := [([8,14,22], 1)]
theorem eval_atom1978 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1978 = ((g 8) * (g 14) * (g 22)) := by
  norm_num [atom1978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1978_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400790402258400 : Int) atom1978) := by
  rw [SparsePolynomial.eval_scale, eval_atom1978]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1978Coded : CoefficientMerge.Poly := [(4966, 1)]
theorem atom1978Coded_decode : atom1978 = SparsePolynomial.decodeCubic 24 atom1978Coded := by decide +kernel
theorem atom1978Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (400790402258400 : Int) atom1978Coded) := by
  have h := atom1978_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1978Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1979 : SparsePolynomial.Poly := [([8,14,23], 1)]
theorem eval_atom1979 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1979 = ((g 8) * (g 14) * (g 23)) := by
  norm_num [atom1979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1979_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510762813976800 : Int) atom1979) := by
  rw [SparsePolynomial.eval_scale, eval_atom1979]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1979Coded : CoefficientMerge.Poly := [(4967, 1)]
theorem atom1979Coded_decode : atom1979 = SparsePolynomial.decodeCubic 24 atom1979Coded := by decide +kernel
theorem atom1979Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510762813976800 : Int) atom1979Coded) := by
  have h := atom1979_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1979Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1980 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom1980 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1980 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom1980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1980_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106212519705600 : Int) atom1980) := by
  rw [SparsePolynomial.eval_scale, eval_atom1980]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1980Coded : CoefficientMerge.Poly := [(4983, 1)]
theorem atom1980Coded_decode : atom1980 = SparsePolynomial.decodeCubic 24 atom1980Coded := by decide +kernel
theorem atom1980Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106212519705600 : Int) atom1980Coded) := by
  have h := atom1980_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1980Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1981 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom1981 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1981 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom1981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1981_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199221120806400 : Int) atom1981) := by
  rw [SparsePolynomial.eval_scale, eval_atom1981]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1981Coded : CoefficientMerge.Poly := [(4984, 1)]
theorem atom1981Coded_decode : atom1981 = SparsePolynomial.decodeCubic 24 atom1981Coded := by decide +kernel
theorem atom1981Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199221120806400 : Int) atom1981Coded) := by
  have h := atom1981_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1981Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1982 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom1982 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1982 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom1982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1982_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199369957248000 : Int) atom1982) := by
  rw [SparsePolynomial.eval_scale, eval_atom1982]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1982Coded : CoefficientMerge.Poly := [(4985, 1)]
theorem atom1982Coded_decode : atom1982 = SparsePolynomial.decodeCubic 24 atom1982Coded := by decide +kernel
theorem atom1982Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199369957248000 : Int) atom1982Coded) := by
  have h := atom1982_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1982Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1983 : SparsePolynomial.Poly := [([8,15,18], 1)]
theorem eval_atom1983 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1983 = ((g 8) * (g 15) * (g 18)) := by
  norm_num [atom1983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1983_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218777971507200 : Int) atom1983) := by
  rw [SparsePolynomial.eval_scale, eval_atom1983]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1983Coded : CoefficientMerge.Poly := [(4986, 1)]
theorem atom1983Coded_decode : atom1983 = SparsePolynomial.decodeCubic 24 atom1983Coded := by decide +kernel
theorem atom1983Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218777971507200 : Int) atom1983Coded) := by
  have h := atom1983_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1983Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1984 : SparsePolynomial.Poly := [([8,15,19], 1)]
theorem eval_atom1984 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1984 = ((g 8) * (g 15) * (g 19)) := by
  norm_num [atom1984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1984_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217143992217600 : Int) atom1984) := by
  rw [SparsePolynomial.eval_scale, eval_atom1984]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1984Coded : CoefficientMerge.Poly := [(4987, 1)]
theorem atom1984Coded_decode : atom1984 = SparsePolynomial.decodeCubic 24 atom1984Coded := by decide +kernel
theorem atom1984Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217143992217600 : Int) atom1984Coded) := by
  have h := atom1984_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1984Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1985 : SparsePolynomial.Poly := [([8,15,20], 1)]
theorem eval_atom1985 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1985 = ((g 8) * (g 15) * (g 20)) := by
  norm_num [atom1985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1985_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (356351811379200 : Int) atom1985) := by
  rw [SparsePolynomial.eval_scale, eval_atom1985]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1985Coded : CoefficientMerge.Poly := [(4988, 1)]
theorem atom1985Coded_decode : atom1985 = SparsePolynomial.decodeCubic 24 atom1985Coded := by decide +kernel
theorem atom1985Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (356351811379200 : Int) atom1985Coded) := by
  have h := atom1985_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1985Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1986 : SparsePolynomial.Poly := [([8,15,21], 1)]
theorem eval_atom1986 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1986 = ((g 8) * (g 15) * (g 21)) := by
  norm_num [atom1986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1986_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399197054995200 : Int) atom1986) := by
  rw [SparsePolynomial.eval_scale, eval_atom1986]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1986Coded : CoefficientMerge.Poly := [(4989, 1)]
theorem atom1986Coded_decode : atom1986 = SparsePolynomial.decodeCubic 24 atom1986Coded := by decide +kernel
theorem atom1986Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399197054995200 : Int) atom1986Coded) := by
  have h := atom1986_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1986Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1987 : SparsePolynomial.Poly := [([8,15,22], 1)]
theorem eval_atom1987 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1987 = ((g 8) * (g 15) * (g 22)) := by
  norm_num [atom1987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1987_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428238524044800 : Int) atom1987) := by
  rw [SparsePolynomial.eval_scale, eval_atom1987]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1987Coded : CoefficientMerge.Poly := [(4990, 1)]
theorem atom1987Coded_decode : atom1987 = SparsePolynomial.decodeCubic 24 atom1987Coded := by decide +kernel
theorem atom1987Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (428238524044800 : Int) atom1987Coded) := by
  have h := atom1987_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1987Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1988 : SparsePolynomial.Poly := [([8,15,23], 1)]
theorem eval_atom1988 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1988 = ((g 8) * (g 15) * (g 23)) := by
  norm_num [atom1988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1988_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (535818438288000 : Int) atom1988) := by
  rw [SparsePolynomial.eval_scale, eval_atom1988]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1988Coded : CoefficientMerge.Poly := [(4991, 1)]
theorem atom1988Coded_decode : atom1988 = SparsePolynomial.decodeCubic 24 atom1988Coded := by decide +kernel
theorem atom1988Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (535818438288000 : Int) atom1988Coded) := by
  have h := atom1988_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1988Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1989 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom1989 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1989 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom1989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1989_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127942640179200 : Int) atom1989) := by
  rw [SparsePolynomial.eval_scale, eval_atom1989]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1989Coded : CoefficientMerge.Poly := [(5008, 1)]
theorem atom1989Coded_decode : atom1989 = SparsePolynomial.decodeCubic 24 atom1989Coded := by decide +kernel
theorem atom1989Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (127942640179200 : Int) atom1989Coded) := by
  have h := atom1989_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1989Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1990 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom1990 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1990 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom1990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1990_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (248889967603200 : Int) atom1990) := by
  rw [SparsePolynomial.eval_scale, eval_atom1990]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1990Coded : CoefficientMerge.Poly := [(5009, 1)]
theorem atom1990Coded_decode : atom1990 = SparsePolynomial.decodeCubic 24 atom1990Coded := by decide +kernel
theorem atom1990Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (248889967603200 : Int) atom1990Coded) := by
  have h := atom1990_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1990Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1991 : SparsePolynomial.Poly := [([8,16,18], 1)]
theorem eval_atom1991 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1991 = ((g 8) * (g 16) * (g 18)) := by
  norm_num [atom1991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1991_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245385868089600 : Int) atom1991) := by
  rw [SparsePolynomial.eval_scale, eval_atom1991]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1991Coded : CoefficientMerge.Poly := [(5010, 1)]
theorem atom1991Coded_decode : atom1991 = SparsePolynomial.decodeCubic 24 atom1991Coded := by decide +kernel
theorem atom1991Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (245385868089600 : Int) atom1991Coded) := by
  have h := atom1991_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1991Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1992 : SparsePolynomial.Poly := [([8,16,19], 1)]
theorem eval_atom1992 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1992 = ((g 8) * (g 16) * (g 19)) := by
  norm_num [atom1992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1992_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (252748761753600 : Int) atom1992) := by
  rw [SparsePolynomial.eval_scale, eval_atom1992]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1992Coded : CoefficientMerge.Poly := [(5011, 1)]
theorem atom1992Coded_decode : atom1992 = SparsePolynomial.decodeCubic 24 atom1992Coded := by decide +kernel
theorem atom1992Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (252748761753600 : Int) atom1992Coded) := by
  have h := atom1992_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1992Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1993 : SparsePolynomial.Poly := [([8,16,20], 1)]
theorem eval_atom1993 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1993 = ((g 8) * (g 16) * (g 20)) := by
  norm_num [atom1993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1993_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400953453868800 : Int) atom1993) := by
  rw [SparsePolynomial.eval_scale, eval_atom1993]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1993Coded : CoefficientMerge.Poly := [(5012, 1)]
theorem atom1993Coded_decode : atom1993 = SparsePolynomial.decodeCubic 24 atom1993Coded := by decide +kernel
theorem atom1993Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (400953453868800 : Int) atom1993Coded) := by
  have h := atom1993_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1993Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1994 : SparsePolynomial.Poly := [([8,16,21], 1)]
theorem eval_atom1994 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1994 = ((g 8) * (g 16) * (g 21)) := by
  norm_num [atom1994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1994_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (452889801302400 : Int) atom1994) := by
  rw [SparsePolynomial.eval_scale, eval_atom1994]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1994Coded : CoefficientMerge.Poly := [(5013, 1)]
theorem atom1994Coded_decode : atom1994 = SparsePolynomial.decodeCubic 24 atom1994Coded := by decide +kernel
theorem atom1994Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (452889801302400 : Int) atom1994Coded) := by
  have h := atom1994_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1994Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1995 : SparsePolynomial.Poly := [([8,16,22], 1)]
theorem eval_atom1995 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1995 = ((g 8) * (g 16) * (g 22)) := by
  norm_num [atom1995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1995_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433229377190400 : Int) atom1995) := by
  rw [SparsePolynomial.eval_scale, eval_atom1995]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1995Coded : CoefficientMerge.Poly := [(5014, 1)]
theorem atom1995Coded_decode : atom1995 = SparsePolynomial.decodeCubic 24 atom1995Coded := by decide +kernel
theorem atom1995Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433229377190400 : Int) atom1995Coded) := by
  have h := atom1995_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1995Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1996 : SparsePolynomial.Poly := [([8,16,23], 1)]
theorem eval_atom1996 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1996 = ((g 8) * (g 16) * (g 23)) := by
  norm_num [atom1996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1996_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (626482301659200 : Int) atom1996) := by
  rw [SparsePolynomial.eval_scale, eval_atom1996]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1996Coded : CoefficientMerge.Poly := [(5015, 1)]
theorem atom1996Coded_decode : atom1996 = SparsePolynomial.decodeCubic 24 atom1996Coded := by decide +kernel
theorem atom1996Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (626482301659200 : Int) atom1996Coded) := by
  have h := atom1996_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1996Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1997 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom1997 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1997 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom1997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1997_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151090250572800 : Int) atom1997) := by
  rw [SparsePolynomial.eval_scale, eval_atom1997]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1997Coded : CoefficientMerge.Poly := [(5033, 1)]
theorem atom1997Coded_decode : atom1997 = SparsePolynomial.decodeCubic 24 atom1997Coded := by decide +kernel
theorem atom1997Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151090250572800 : Int) atom1997Coded) := by
  have h := atom1997_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1997Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1998 : SparsePolynomial.Poly := [([8,17,18], 1)]
theorem eval_atom1998 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1998 = ((g 8) * (g 17) * (g 18)) := by
  norm_num [atom1998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1998_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (286892872358400 : Int) atom1998) := by
  rw [SparsePolynomial.eval_scale, eval_atom1998]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1998Coded : CoefficientMerge.Poly := [(5034, 1)]
theorem atom1998Coded_decode : atom1998 = SparsePolynomial.decodeCubic 24 atom1998Coded := by decide +kernel
theorem atom1998Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (286892872358400 : Int) atom1998Coded) := by
  have h := atom1998_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1998Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1999 : SparsePolynomial.Poly := [([8,17,19], 1)]
theorem eval_atom1999 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1999 = ((g 8) * (g 17) * (g 19)) := by
  norm_num [atom1999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1999_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308219008204800 : Int) atom1999) := by
  rw [SparsePolynomial.eval_scale, eval_atom1999]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1999Coded : CoefficientMerge.Poly := [(5035, 1)]
theorem atom1999Coded_decode : atom1999 = SparsePolynomial.decodeCubic 24 atom1999Coded := by decide +kernel
theorem atom1999Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (308219008204800 : Int) atom1999Coded) := by
  have h := atom1999_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1999Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2000 : SparsePolynomial.Poly := [([8,17,20], 1)]
theorem eval_atom2000 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2000 = ((g 8) * (g 17) * (g 20)) := by
  norm_num [atom2000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470386942502400 : Int) atom2000) := by
  rw [SparsePolynomial.eval_scale, eval_atom2000]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2000Coded : CoefficientMerge.Poly := [(5036, 1)]
theorem atom2000Coded_decode : atom2000 = SparsePolynomial.decodeCubic 24 atom2000Coded := by decide +kernel
theorem atom2000Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (470386942502400 : Int) atom2000Coded) := by
  have h := atom2000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2001 : SparsePolynomial.Poly := [([8,17,21], 1)]
theorem eval_atom2001 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2001 = ((g 8) * (g 17) * (g 21)) := by
  norm_num [atom2001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2001_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (533897578368000 : Int) atom2001) := by
  rw [SparsePolynomial.eval_scale, eval_atom2001]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2001Coded : CoefficientMerge.Poly := [(5037, 1)]
theorem atom2001Coded_decode : atom2001 = SparsePolynomial.decodeCubic 24 atom2001Coded := by decide +kernel
theorem atom2001Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (533897578368000 : Int) atom2001Coded) := by
  have h := atom2001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2002 : SparsePolynomial.Poly := [([8,17,22], 1)]
theorem eval_atom2002 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2002 = ((g 8) * (g 17) * (g 22)) := by
  norm_num [atom2002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2002_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524687759769600 : Int) atom2002) := by
  rw [SparsePolynomial.eval_scale, eval_atom2002]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2002Coded : CoefficientMerge.Poly := [(5038, 1)]
theorem atom2002Coded_decode : atom2002 = SparsePolynomial.decodeCubic 24 atom2002Coded := by decide +kernel
theorem atom2002Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (524687759769600 : Int) atom2002Coded) := by
  have h := atom2002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2003 : SparsePolynomial.Poly := [([8,17,23], 1)]
theorem eval_atom2003 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2003 = ((g 8) * (g 17) * (g 23)) := by
  norm_num [atom2003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (728320495795200 : Int) atom2003) := by
  rw [SparsePolynomial.eval_scale, eval_atom2003]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2003Coded : CoefficientMerge.Poly := [(5039, 1)]
theorem atom2003Coded_decode : atom2003 = SparsePolynomial.decodeCubic 24 atom2003Coded := by decide +kernel
theorem atom2003Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (728320495795200 : Int) atom2003Coded) := by
  have h := atom2003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2004 : SparsePolynomial.Poly := [([8,18,18], 1)]
theorem eval_atom2004 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2004 = ((g 8) * (g 18) * (g 18)) := by
  norm_num [atom2004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182186435692800 : Int) atom2004) := by
  rw [SparsePolynomial.eval_scale, eval_atom2004]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2004Coded : CoefficientMerge.Poly := [(5058, 1)]
theorem atom2004Coded_decode : atom2004 = SparsePolynomial.decodeCubic 24 atom2004Coded := by decide +kernel
theorem atom2004Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (182186435692800 : Int) atom2004Coded) := by
  have h := atom2004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2005 : SparsePolynomial.Poly := [([8,18,19], 1)]
theorem eval_atom2005 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2005 = ((g 8) * (g 18) * (g 19)) := by
  norm_num [atom2005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (362650621132800 : Int) atom2005) := by
  rw [SparsePolynomial.eval_scale, eval_atom2005]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2005Coded : CoefficientMerge.Poly := [(5059, 1)]
theorem atom2005Coded_decode : atom2005 = SparsePolynomial.decodeCubic 24 atom2005Coded := by decide +kernel
theorem atom2005Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (362650621132800 : Int) atom2005Coded) := by
  have h := atom2005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2006 : SparsePolynomial.Poly := [([8,18,20], 1)]
theorem eval_atom2006 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2006 = ((g 8) * (g 18) * (g 20)) := by
  norm_num [atom2006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572191068556800 : Int) atom2006) := by
  rw [SparsePolynomial.eval_scale, eval_atom2006]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2006Coded : CoefficientMerge.Poly := [(5060, 1)]
theorem atom2006Coded_decode : atom2006 = SparsePolynomial.decodeCubic 24 atom2006Coded := by decide +kernel
theorem atom2006Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (572191068556800 : Int) atom2006Coded) := by
  have h := atom2006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2007 : SparsePolynomial.Poly := [([8,18,21], 1)]
theorem eval_atom2007 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2007 = ((g 8) * (g 18) * (g 21)) := by
  norm_num [atom2007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592299934934400 : Int) atom2007) := by
  rw [SparsePolynomial.eval_scale, eval_atom2007]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2007Coded : CoefficientMerge.Poly := [(5061, 1)]
theorem atom2007Coded_decode : atom2007 = SparsePolynomial.decodeCubic 24 atom2007Coded := by decide +kernel
theorem atom2007Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (592299934934400 : Int) atom2007Coded) := by
  have h := atom2007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2008 : SparsePolynomial.Poly := [([8,18,22], 1)]
theorem eval_atom2008 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2008 = ((g 8) * (g 18) * (g 22)) := by
  norm_num [atom2008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483171412953600 : Int) atom2008) := by
  rw [SparsePolynomial.eval_scale, eval_atom2008]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2008Coded : CoefficientMerge.Poly := [(5062, 1)]
theorem atom2008Coded_decode : atom2008 = SparsePolynomial.decodeCubic 24 atom2008Coded := by decide +kernel
theorem atom2008Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (483171412953600 : Int) atom2008Coded) := by
  have h := atom2008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2009 : SparsePolynomial.Poly := [([8,18,23], 1)]
theorem eval_atom2009 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2009 = ((g 8) * (g 18) * (g 23)) := by
  norm_num [atom2009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (706816287777600 : Int) atom2009) := by
  rw [SparsePolynomial.eval_scale, eval_atom2009]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2009Coded : CoefficientMerge.Poly := [(5063, 1)]
theorem atom2009Coded_decode : atom2009 = SparsePolynomial.decodeCubic 24 atom2009Coded := by decide +kernel
theorem atom2009Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (706816287777600 : Int) atom2009Coded) := by
  have h := atom2009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2010 : SparsePolynomial.Poly := [([8,19,19], 1)]
theorem eval_atom2010 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2010 = ((g 8) * (g 19) * (g 19)) := by
  norm_num [atom2010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117725372835840 : Int) atom2010) := by
  rw [SparsePolynomial.eval_scale, eval_atom2010]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2010Coded : CoefficientMerge.Poly := [(5083, 1)]
theorem atom2010Coded_decode : atom2010 = SparsePolynomial.decodeCubic 24 atom2010Coded := by decide +kernel
theorem atom2010Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (117725372835840 : Int) atom2010Coded) := by
  have h := atom2010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2011 : SparsePolynomial.Poly := [([8,19,20], 1)]
theorem eval_atom2011 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2011 = ((g 8) * (g 19) * (g 20)) := by
  norm_num [atom2011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415423770854400 : Int) atom2011) := by
  rw [SparsePolynomial.eval_scale, eval_atom2011]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2011Coded : CoefficientMerge.Poly := [(5084, 1)]
theorem atom2011Coded_decode : atom2011 = SparsePolynomial.decodeCubic 24 atom2011Coded := by decide +kernel
theorem atom2011Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415423770854400 : Int) atom2011Coded) := by
  have h := atom2011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2012 : SparsePolynomial.Poly := [([8,19,21], 1)]
theorem eval_atom2012 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2012 = ((g 8) * (g 19) * (g 21)) := by
  norm_num [atom2012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433879489612800 : Int) atom2012) := by
  rw [SparsePolynomial.eval_scale, eval_atom2012]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2012Coded : CoefficientMerge.Poly := [(5085, 1)]
theorem atom2012Coded_decode : atom2012 = SparsePolynomial.decodeCubic 24 atom2012Coded := by decide +kernel
theorem atom2012Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433879489612800 : Int) atom2012Coded) := by
  have h := atom2012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2013 : SparsePolynomial.Poly := [([8,19,22], 1)]
theorem eval_atom2013 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2013 = ((g 8) * (g 19) * (g 22)) := by
  norm_num [atom2013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (392141176761600 : Int) atom2013) := by
  rw [SparsePolynomial.eval_scale, eval_atom2013]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2013Coded : CoefficientMerge.Poly := [(5086, 1)]
theorem atom2013Coded_decode : atom2013 = SparsePolynomial.decodeCubic 24 atom2013Coded := by decide +kernel
theorem atom2013Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (392141176761600 : Int) atom2013Coded) := by
  have h := atom2013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2014 : SparsePolynomial.Poly := [([8,19,23], 1)]
theorem eval_atom2014 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2014 = ((g 8) * (g 19) * (g 23)) := by
  norm_num [atom2014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464228593113600 : Int) atom2014) := by
  rw [SparsePolynomial.eval_scale, eval_atom2014]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2014Coded : CoefficientMerge.Poly := [(5087, 1)]
theorem atom2014Coded_decode : atom2014 = SparsePolynomial.decodeCubic 24 atom2014Coded := by decide +kernel
theorem atom2014Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (464228593113600 : Int) atom2014Coded) := by
  have h := atom2014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2015 : SparsePolynomial.Poly := [([8,20,20], 1)]
theorem eval_atom2015 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2015 = ((g 8) * (g 20) * (g 20)) := by
  norm_num [atom2015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305380484640000 : Int) atom2015) := by
  rw [SparsePolynomial.eval_scale, eval_atom2015]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2015Coded : CoefficientMerge.Poly := [(5108, 1)]
theorem atom2015Coded_decode : atom2015 = SparsePolynomial.decodeCubic 24 atom2015Coded := by decide +kernel
theorem atom2015Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (305380484640000 : Int) atom2015Coded) := by
  have h := atom2015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2016 : SparsePolynomial.Poly := [([8,20,21], 1)]
theorem eval_atom2016 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2016 = ((g 8) * (g 20) * (g 21)) := by
  norm_num [atom2016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (451511292355200 : Int) atom2016) := by
  rw [SparsePolynomial.eval_scale, eval_atom2016]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2016Coded : CoefficientMerge.Poly := [(5109, 1)]
theorem atom2016Coded_decode : atom2016 = SparsePolynomial.decodeCubic 24 atom2016Coded := by decide +kernel
theorem atom2016Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (451511292355200 : Int) atom2016Coded) := by
  have h := atom2016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2017 : SparsePolynomial.Poly := [([8,20,22], 1)]
theorem eval_atom2017 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2017 = ((g 8) * (g 20) * (g 22)) := by
  norm_num [atom2017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (376656388012800 : Int) atom2017) := by
  rw [SparsePolynomial.eval_scale, eval_atom2017]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2017Coded : CoefficientMerge.Poly := [(5110, 1)]
theorem atom2017Coded_decode : atom2017 = SparsePolynomial.decodeCubic 24 atom2017Coded := by decide +kernel
theorem atom2017Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (376656388012800 : Int) atom2017Coded) := by
  have h := atom2017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2018 : SparsePolynomial.Poly := [([8,20,23], 1)]
theorem eval_atom2018 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2018 = ((g 8) * (g 20) * (g 23)) := by
  norm_num [atom2018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472146160248000 : Int) atom2018) := by
  rw [SparsePolynomial.eval_scale, eval_atom2018]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2018Coded : CoefficientMerge.Poly := [(5111, 1)]
theorem atom2018Coded_decode : atom2018 = SparsePolynomial.decodeCubic 24 atom2018Coded := by decide +kernel
theorem atom2018Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472146160248000 : Int) atom2018Coded) := by
  have h := atom2018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2019 : SparsePolynomial.Poly := [([8,21,21], 1)]
theorem eval_atom2019 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2019 = ((g 8) * (g 21) * (g 21)) := by
  norm_num [atom2019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88951036204800 : Int) atom2019) := by
  rw [SparsePolynomial.eval_scale, eval_atom2019]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 8) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2019Coded : CoefficientMerge.Poly := [(5133, 1)]
theorem atom2019Coded_decode : atom2019 = SparsePolynomial.decodeCubic 24 atom2019Coded := by decide +kernel
theorem atom2019Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88951036204800 : Int) atom2019Coded) := by
  have h := atom2019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2020 : SparsePolynomial.Poly := [([8,21,22], 1)]
theorem eval_atom2020 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2020 = ((g 8) * (g 21) * (g 22)) := by
  norm_num [atom2020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158310267696000 : Int) atom2020) := by
  rw [SparsePolynomial.eval_scale, eval_atom2020]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 8) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2020Coded : CoefficientMerge.Poly := [(5134, 1)]
theorem atom2020Coded_decode : atom2020 = SparsePolynomial.decodeCubic 24 atom2020Coded := by decide +kernel
theorem atom2020Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158310267696000 : Int) atom2020Coded) := by
  have h := atom2020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2021 : SparsePolynomial.Poly := [([8,21,23], 1)]
theorem eval_atom2021 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2021 = ((g 8) * (g 21) * (g 23)) := by
  norm_num [atom2021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (243917316316800 : Int) atom2021) := by
  rw [SparsePolynomial.eval_scale, eval_atom2021]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 8) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2021Coded : CoefficientMerge.Poly := [(5135, 1)]
theorem atom2021Coded_decode : atom2021 = SparsePolynomial.decodeCubic 24 atom2021Coded := by decide +kernel
theorem atom2021Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (243917316316800 : Int) atom2021Coded) := by
  have h := atom2021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2022 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom2022 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2022 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom2022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17430917842800 : Int) atom2022) := by
  rw [SparsePolynomial.eval_scale, eval_atom2022]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2022Coded : CoefficientMerge.Poly := [(5409, 1)]
theorem atom2022Coded_decode : atom2022 = SparsePolynomial.decodeCubic 24 atom2022Coded := by decide +kernel
theorem atom2022Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17430917842800 : Int) atom2022Coded) := by
  have h := atom2022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2023 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom2023 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2023 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom2023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24545388344400 : Int) atom2023) := by
  rw [SparsePolynomial.eval_scale, eval_atom2023]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2023Coded : CoefficientMerge.Poly := [(5410, 1)]
theorem atom2023Coded_decode : atom2023 = SparsePolynomial.decodeCubic 24 atom2023Coded := by decide +kernel
theorem atom2023Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24545388344400 : Int) atom2023Coded) := by
  have h := atom2023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2024 : SparsePolynomial.Poly := [([9,9,11], 1)]
theorem eval_atom2024 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2024 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom2024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2024) := by
  rw [SparsePolynomial.eval_scale, eval_atom2024]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2024Coded : CoefficientMerge.Poly := [(5411, 1)]
theorem atom2024Coded_decode : atom2024 = SparsePolynomial.decodeCubic 24 atom2024Coded := by decide +kernel
theorem atom2024Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2024Coded) := by
  have h := atom2024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2025 : SparsePolynomial.Poly := [([9,9,12], 1)]
theorem eval_atom2025 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2025 = ((g 9) * (g 9) * (g 12)) := by
  norm_num [atom2025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2025) := by
  rw [SparsePolynomial.eval_scale, eval_atom2025]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2025Coded : CoefficientMerge.Poly := [(5412, 1)]
theorem atom2025Coded_decode : atom2025 = SparsePolynomial.decodeCubic 24 atom2025Coded := by decide +kernel
theorem atom2025Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2025Coded) := by
  have h := atom2025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2026 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom2026 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2026 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom2026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16316859358800 : Int) atom2026) := by
  rw [SparsePolynomial.eval_scale, eval_atom2026]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2026Coded : CoefficientMerge.Poly := [(5434, 1)]
theorem atom2026Coded_decode : atom2026 = SparsePolynomial.decodeCubic 24 atom2026Coded := by decide +kernel
theorem atom2026Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16316859358800 : Int) atom2026Coded) := by
  have h := atom2026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2027 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom2027 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2027 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom2027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2027) := by
  rw [SparsePolynomial.eval_scale, eval_atom2027]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2027Coded : CoefficientMerge.Poly := [(5438, 1)]
theorem atom2027Coded_decode : atom2027 = SparsePolynomial.decodeCubic 24 atom2027Coded := by decide +kernel
theorem atom2027Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2027Coded) := by
  have h := atom2027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2028 : SparsePolynomial.Poly := [([9,10,15], 1)]
theorem eval_atom2028 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2028 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom2028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2028) := by
  rw [SparsePolynomial.eval_scale, eval_atom2028]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2028Coded : CoefficientMerge.Poly := [(5439, 1)]
theorem atom2028Coded_decode : atom2028 = SparsePolynomial.decodeCubic 24 atom2028Coded := by decide +kernel
theorem atom2028Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2028Coded) := by
  have h := atom2028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2029 : SparsePolynomial.Poly := [([9,10,16], 1)]
theorem eval_atom2029 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2029 = ((g 9) * (g 10) * (g 16)) := by
  norm_num [atom2029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom2029) := by
  rw [SparsePolynomial.eval_scale, eval_atom2029]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2029Coded : CoefficientMerge.Poly := [(5440, 1)]
theorem atom2029Coded_decode : atom2029 = SparsePolynomial.decodeCubic 24 atom2029Coded := by decide +kernel
theorem atom2029Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom2029Coded) := by
  have h := atom2029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2030 : SparsePolynomial.Poly := [([9,10,17], 1)]
theorem eval_atom2030 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2030 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom2030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom2030) := by
  rw [SparsePolynomial.eval_scale, eval_atom2030]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2030Coded : CoefficientMerge.Poly := [(5441, 1)]
theorem atom2030Coded_decode : atom2030 = SparsePolynomial.decodeCubic 24 atom2030Coded := by decide +kernel
theorem atom2030Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12332162304000 : Int) atom2030Coded) := by
  have h := atom2030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2031 : SparsePolynomial.Poly := [([9,10,19], 1)]
theorem eval_atom2031 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2031 = ((g 9) * (g 10) * (g 19)) := by
  norm_num [atom2031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1197778982400 : Int) atom2031) := by
  rw [SparsePolynomial.eval_scale, eval_atom2031]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2031Coded : CoefficientMerge.Poly := [(5443, 1)]
theorem atom2031Coded_decode : atom2031 = SparsePolynomial.decodeCubic 24 atom2031Coded := by decide +kernel
theorem atom2031Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1197778982400 : Int) atom2031Coded) := by
  have h := atom2031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2032 : SparsePolynomial.Poly := [([9,10,21], 1)]
theorem eval_atom2032 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2032 = ((g 9) * (g 10) * (g 21)) := by
  norm_num [atom2032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45125791603200 : Int) atom2032) := by
  rw [SparsePolynomial.eval_scale, eval_atom2032]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2032Coded : CoefficientMerge.Poly := [(5445, 1)]
theorem atom2032Coded_decode : atom2032 = SparsePolynomial.decodeCubic 24 atom2032Coded := by decide +kernel
theorem atom2032Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45125791603200 : Int) atom2032Coded) := by
  have h := atom2032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2033 : SparsePolynomial.Poly := [([9,10,22], 1)]
theorem eval_atom2033 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2033 = ((g 9) * (g 10) * (g 22)) := by
  norm_num [atom2033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87856025241600 : Int) atom2033) := by
  rw [SparsePolynomial.eval_scale, eval_atom2033]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2033Coded : CoefficientMerge.Poly := [(5446, 1)]
theorem atom2033Coded_decode : atom2033 = SparsePolynomial.decodeCubic 24 atom2033Coded := by decide +kernel
theorem atom2033Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87856025241600 : Int) atom2033Coded) := by
  have h := atom2033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2034 : SparsePolynomial.Poly := [([9,10,23], 1)]
theorem eval_atom2034 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2034 = ((g 9) * (g 10) * (g 23)) := by
  norm_num [atom2034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137822544921600 : Int) atom2034) := by
  rw [SparsePolynomial.eval_scale, eval_atom2034]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2034Coded : CoefficientMerge.Poly := [(5447, 1)]
theorem atom2034Coded_decode : atom2034 = SparsePolynomial.decodeCubic 24 atom2034Coded := by decide +kernel
theorem atom2034Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137822544921600 : Int) atom2034Coded) := by
  have h := atom2034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2035 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom2035 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2035 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom2035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2035_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9368057991600 : Int) atom2035) := by
  rw [SparsePolynomial.eval_scale, eval_atom2035]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2035Coded : CoefficientMerge.Poly := [(5459, 1)]
theorem atom2035Coded_decode : atom2035 = SparsePolynomial.decodeCubic 24 atom2035Coded := by decide +kernel
theorem atom2035Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9368057991600 : Int) atom2035Coded) := by
  have h := atom2035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2036 : SparsePolynomial.Poly := [([9,11,12], 1)]
theorem eval_atom2036 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2036 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom2036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2036_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1020592742400 : Int) atom2036) := by
  rw [SparsePolynomial.eval_scale, eval_atom2036]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2036Coded : CoefficientMerge.Poly := [(5460, 1)]
theorem atom2036Coded_decode : atom2036 = SparsePolynomial.decodeCubic 24 atom2036Coded := by decide +kernel
theorem atom2036Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1020592742400 : Int) atom2036Coded) := by
  have h := atom2036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2037 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom2037 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2037 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom2037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2037_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2062447833600 : Int) atom2037) := by
  rw [SparsePolynomial.eval_scale, eval_atom2037]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2037Coded : CoefficientMerge.Poly := [(5462, 1)]
theorem atom2037Coded_decode : atom2037 = SparsePolynomial.decodeCubic 24 atom2037Coded := by decide +kernel
theorem atom2037Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2062447833600 : Int) atom2037Coded) := by
  have h := atom2037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2038 : SparsePolynomial.Poly := [([9,11,15], 1)]
theorem eval_atom2038 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2038 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom2038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2038_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4124895667200 : Int) atom2038) := by
  rw [SparsePolynomial.eval_scale, eval_atom2038]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2038Coded : CoefficientMerge.Poly := [(5463, 1)]
theorem atom2038Coded_decode : atom2038 = SparsePolynomial.decodeCubic 24 atom2038Coded := by decide +kernel
theorem atom2038Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4124895667200 : Int) atom2038Coded) := by
  have h := atom2038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2039 : SparsePolynomial.Poly := [([9,11,16], 1)]
theorem eval_atom2039 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2039 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom2039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2039_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9270384076800 : Int) atom2039) := by
  rw [SparsePolynomial.eval_scale, eval_atom2039]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2039Coded : CoefficientMerge.Poly := [(5464, 1)]
theorem atom2039Coded_decode : atom2039 = SparsePolynomial.decodeCubic 24 atom2039Coded := by decide +kernel
theorem atom2039Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9270384076800 : Int) atom2039Coded) := by
  have h := atom2039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2040 : SparsePolynomial.Poly := [([9,11,17], 1)]
theorem eval_atom2040 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2040 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom2040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2040_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14415872486400 : Int) atom2040) := by
  rw [SparsePolynomial.eval_scale, eval_atom2040]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2040Coded : CoefficientMerge.Poly := [(5465, 1)]
theorem atom2040Coded_decode : atom2040 = SparsePolynomial.decodeCubic 24 atom2040Coded := by decide +kernel
theorem atom2040Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14415872486400 : Int) atom2040Coded) := by
  have h := atom2040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2041 : SparsePolynomial.Poly := [([9,11,18], 1)]
theorem eval_atom2041 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2041 = ((g 9) * (g 11) * (g 18)) := by
  norm_num [atom2041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2041_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5671037984832 : Int) atom2041) := by
  rw [SparsePolynomial.eval_scale, eval_atom2041]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2041Coded : CoefficientMerge.Poly := [(5466, 1)]
theorem atom2041Coded_decode : atom2041 = SparsePolynomial.decodeCubic 24 atom2041Coded := by decide +kernel
theorem atom2041Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5671037984832 : Int) atom2041Coded) := by
  have h := atom2041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2042 : SparsePolynomial.Poly := [([9,11,20], 1)]
theorem eval_atom2042 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2042 = ((g 9) * (g 11) * (g 20)) := by
  norm_num [atom2042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2042_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5317070501952 : Int) atom2042) := by
  rw [SparsePolynomial.eval_scale, eval_atom2042]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2042Coded : CoefficientMerge.Poly := [(5468, 1)]
theorem atom2042Coded_decode : atom2042 = SparsePolynomial.decodeCubic 24 atom2042Coded := by decide +kernel
theorem atom2042Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5317070501952 : Int) atom2042Coded) := by
  have h := atom2042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2043 : SparsePolynomial.Poly := [([9,11,21], 1)]
theorem eval_atom2043 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2043 = ((g 9) * (g 11) * (g 21)) := by
  norm_num [atom2043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2043_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90503187667200 : Int) atom2043) := by
  rw [SparsePolynomial.eval_scale, eval_atom2043]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2043Coded : CoefficientMerge.Poly := [(5469, 1)]
theorem atom2043Coded_decode : atom2043 = SparsePolynomial.decodeCubic 24 atom2043Coded := by decide +kernel
theorem atom2043Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90503187667200 : Int) atom2043Coded) := by
  have h := atom2043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2044 : SparsePolynomial.Poly := [([9,11,22], 1)]
theorem eval_atom2044 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2044 = ((g 9) * (g 11) * (g 22)) := by
  norm_num [atom2044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2044_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175048665200640 : Int) atom2044) := by
  rw [SparsePolynomial.eval_scale, eval_atom2044]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2044Coded : CoefficientMerge.Poly := [(5470, 1)]
theorem atom2044Coded_decode : atom2044 = SparsePolynomial.decodeCubic 24 atom2044Coded := by decide +kernel
theorem atom2044Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175048665200640 : Int) atom2044Coded) := by
  have h := atom2044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2045 : SparsePolynomial.Poly := [([9,11,23], 1)]
theorem eval_atom2045 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2045 = ((g 9) * (g 11) * (g 23)) := by
  norm_num [atom2045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2045_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272556733680000 : Int) atom2045) := by
  rw [SparsePolynomial.eval_scale, eval_atom2045]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2045Coded : CoefficientMerge.Poly := [(5471, 1)]
theorem atom2045Coded_decode : atom2045 = SparsePolynomial.decodeCubic 24 atom2045Coded := by decide +kernel
theorem atom2045Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (272556733680000 : Int) atom2045Coded) := by
  have h := atom2045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2046 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom2046 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2046 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom2046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2046_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17337452101200 : Int) atom2046) := by
  rw [SparsePolynomial.eval_scale, eval_atom2046]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2046Coded : CoefficientMerge.Poly := [(5484, 1)]
theorem atom2046Coded_decode : atom2046 = SparsePolynomial.decodeCubic 24 atom2046Coded := by decide +kernel
theorem atom2046Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17337452101200 : Int) atom2046Coded) := by
  have h := atom2046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2047 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom2047 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2047 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom2047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2047_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25965314575200 : Int) atom2047) := by
  rw [SparsePolynomial.eval_scale, eval_atom2047]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2047Coded : CoefficientMerge.Poly := [(5485, 1)]
theorem atom2047Coded_decode : atom2047 = SparsePolynomial.decodeCubic 24 atom2047Coded := by decide +kernel
theorem atom2047Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25965314575200 : Int) atom2047Coded) := by
  have h := atom2047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2048 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom2048 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2048 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom2048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2048_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32152658076000 : Int) atom2048) := by
  rw [SparsePolynomial.eval_scale, eval_atom2048]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2048Coded : CoefficientMerge.Poly := [(5486, 1)]
theorem atom2048Coded_decode : atom2048 = SparsePolynomial.decodeCubic 24 atom2048Coded := by decide +kernel
theorem atom2048Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (32152658076000 : Int) atom2048Coded) := by
  have h := atom2048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block027 : CoefficientMerge.Poly := [(4943, 476282593155600), (4958, 79390066694400), (4959, 153751587897600), (4960, 156940940217600), (4961, 160130292537600), (4962, 174436309555200), (4963, 177035188730400), (4964, 282193893273600), (4965, 312992405510400), (4966, 400790402258400), (4967, 510762813976800), (4983, 106212519705600), (4984, 199221120806400), (4985, 199369957248000), (4986, 218777971507200), (4987, 217143992217600), (4988, 356351811379200), (4989, 399197054995200), (4990, 428238524044800), (4991, 535818438288000), (5008, 127942640179200), (5009, 248889967603200), (5010, 245385868089600), (5011, 252748761753600), (5012, 400953453868800), (5013, 452889801302400), (5014, 433229377190400), (5015, 626482301659200), (5033, 151090250572800), (5034, 286892872358400), (5035, 308219008204800), (5036, 470386942502400), (5037, 533897578368000), (5038, 524687759769600), (5039, 728320495795200), (5058, 182186435692800), (5059, 362650621132800), (5060, 572191068556800), (5061, 592299934934400), (5062, 483171412953600), (5063, 706816287777600), (5083, 117725372835840), (5084, 415423770854400), (5085, 433879489612800), (5086, 392141176761600), (5087, 464228593113600), (5108, 305380484640000), (5109, 451511292355200), (5110, 376656388012800), (5111, 472146160248000), (5133, 88951036204800), (5134, 158310267696000), (5135, 243917316316800), (5409, 17430917842800), (5410, 24545388344400), (5411, 3083040576000), (5412, 3083040576000), (5434, 16316859358800), (5438, 3083040576000), (5439, 6166081152000), (5440, 9249121728000), (5441, 12332162304000), (5443, 1197778982400), (5445, 45125791603200), (5446, 87856025241600), (5447, 137822544921600), (5459, 9368057991600), (5460, 1020592742400), (5462, 2062447833600), (5463, 4124895667200), (5464, 9270384076800), (5465, 14415872486400), (5466, 5671037984832), (5468, 5317070501952), (5469, 90503187667200), (5470, 175048665200640), (5471, 272556733680000), (5484, 17337452101200), (5485, 25965314575200), (5486, 32152658076000)]
theorem block027_data : block027 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476282593155600 : Int) atom1969Coded) (CoefficientMerge.scale (79390066694400 : Int) atom1970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153751587897600 : Int) atom1971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156940940217600 : Int) atom1972Coded) (CoefficientMerge.scale (160130292537600 : Int) atom1973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174436309555200 : Int) atom1974Coded) (CoefficientMerge.scale (177035188730400 : Int) atom1975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (282193893273600 : Int) atom1976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (312992405510400 : Int) atom1977Coded) (CoefficientMerge.scale (400790402258400 : Int) atom1978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510762813976800 : Int) atom1979Coded) (CoefficientMerge.scale (106212519705600 : Int) atom1980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199221120806400 : Int) atom1981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199369957248000 : Int) atom1982Coded) (CoefficientMerge.scale (218777971507200 : Int) atom1983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217143992217600 : Int) atom1984Coded) (CoefficientMerge.scale (356351811379200 : Int) atom1985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399197054995200 : Int) atom1986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (428238524044800 : Int) atom1987Coded) (CoefficientMerge.scale (535818438288000 : Int) atom1988Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (127942640179200 : Int) atom1989Coded) (CoefficientMerge.scale (248889967603200 : Int) atom1990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245385868089600 : Int) atom1991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (252748761753600 : Int) atom1992Coded) (CoefficientMerge.scale (400953453868800 : Int) atom1993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (452889801302400 : Int) atom1994Coded) (CoefficientMerge.scale (433229377190400 : Int) atom1995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (626482301659200 : Int) atom1996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (151090250572800 : Int) atom1997Coded) (CoefficientMerge.scale (286892872358400 : Int) atom1998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (308219008204800 : Int) atom1999Coded) (CoefficientMerge.scale (470386942502400 : Int) atom2000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (533897578368000 : Int) atom2001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524687759769600 : Int) atom2002Coded) (CoefficientMerge.scale (728320495795200 : Int) atom2003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182186435692800 : Int) atom2004Coded) (CoefficientMerge.scale (362650621132800 : Int) atom2005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572191068556800 : Int) atom2006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (592299934934400 : Int) atom2007Coded) (CoefficientMerge.scale (483171412953600 : Int) atom2008Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (706816287777600 : Int) atom2009Coded) (CoefficientMerge.scale (117725372835840 : Int) atom2010Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415423770854400 : Int) atom2011Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433879489612800 : Int) atom2012Coded) (CoefficientMerge.scale (392141176761600 : Int) atom2013Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (464228593113600 : Int) atom2014Coded) (CoefficientMerge.scale (305380484640000 : Int) atom2015Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (451511292355200 : Int) atom2016Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (376656388012800 : Int) atom2017Coded) (CoefficientMerge.scale (472146160248000 : Int) atom2018Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88951036204800 : Int) atom2019Coded) (CoefficientMerge.scale (158310267696000 : Int) atom2020Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243917316316800 : Int) atom2021Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17430917842800 : Int) atom2022Coded) (CoefficientMerge.scale (24545388344400 : Int) atom2023Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2024Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2025Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16316859358800 : Int) atom2026Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2027Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2028Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom2029Coded) (CoefficientMerge.scale (12332162304000 : Int) atom2030Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1197778982400 : Int) atom2031Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45125791603200 : Int) atom2032Coded) (CoefficientMerge.scale (87856025241600 : Int) atom2033Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137822544921600 : Int) atom2034Coded) (CoefficientMerge.scale (9368057991600 : Int) atom2035Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1020592742400 : Int) atom2036Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2062447833600 : Int) atom2037Coded) (CoefficientMerge.scale (4124895667200 : Int) atom2038Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9270384076800 : Int) atom2039Coded) (CoefficientMerge.scale (14415872486400 : Int) atom2040Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5671037984832 : Int) atom2041Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5317070501952 : Int) atom2042Coded) (CoefficientMerge.scale (90503187667200 : Int) atom2043Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175048665200640 : Int) atom2044Coded) (CoefficientMerge.scale (272556733680000 : Int) atom2045Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17337452101200 : Int) atom2046Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25965314575200 : Int) atom2047Coded) (CoefficientMerge.scale (32152658076000 : Int) atom2048Coded)))))))) := by decide +kernel
theorem block027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block027 := by
  rw [block027_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1969Coded_nonneg g hg hA hB) (atom1970Coded_nonneg g hg hA hB)) (add_nonneg (atom1971Coded_nonneg g hg hA hB) (add_nonneg (atom1972Coded_nonneg g hg hA hB) (atom1973Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1974Coded_nonneg g hg hA hB) (atom1975Coded_nonneg g hg hA hB)) (add_nonneg (atom1976Coded_nonneg g hg hA hB) (add_nonneg (atom1977Coded_nonneg g hg hA hB) (atom1978Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1979Coded_nonneg g hg hA hB) (atom1980Coded_nonneg g hg hA hB)) (add_nonneg (atom1981Coded_nonneg g hg hA hB) (add_nonneg (atom1982Coded_nonneg g hg hA hB) (atom1983Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1984Coded_nonneg g hg hA hB) (atom1985Coded_nonneg g hg hA hB)) (add_nonneg (atom1986Coded_nonneg g hg hA hB) (add_nonneg (atom1987Coded_nonneg g hg hA hB) (atom1988Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1989Coded_nonneg g hg hA hB) (atom1990Coded_nonneg g hg hA hB)) (add_nonneg (atom1991Coded_nonneg g hg hA hB) (add_nonneg (atom1992Coded_nonneg g hg hA hB) (atom1993Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1994Coded_nonneg g hg hA hB) (atom1995Coded_nonneg g hg hA hB)) (add_nonneg (atom1996Coded_nonneg g hg hA hB) (add_nonneg (atom1997Coded_nonneg g hg hA hB) (atom1998Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1999Coded_nonneg g hg hA hB) (atom2000Coded_nonneg g hg hA hB)) (add_nonneg (atom2001Coded_nonneg g hg hA hB) (add_nonneg (atom2002Coded_nonneg g hg hA hB) (atom2003Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2004Coded_nonneg g hg hA hB) (atom2005Coded_nonneg g hg hA hB)) (add_nonneg (atom2006Coded_nonneg g hg hA hB) (add_nonneg (atom2007Coded_nonneg g hg hA hB) (atom2008Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2009Coded_nonneg g hg hA hB) (atom2010Coded_nonneg g hg hA hB)) (add_nonneg (atom2011Coded_nonneg g hg hA hB) (add_nonneg (atom2012Coded_nonneg g hg hA hB) (atom2013Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2014Coded_nonneg g hg hA hB) (atom2015Coded_nonneg g hg hA hB)) (add_nonneg (atom2016Coded_nonneg g hg hA hB) (add_nonneg (atom2017Coded_nonneg g hg hA hB) (atom2018Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2019Coded_nonneg g hg hA hB) (atom2020Coded_nonneg g hg hA hB)) (add_nonneg (atom2021Coded_nonneg g hg hA hB) (add_nonneg (atom2022Coded_nonneg g hg hA hB) (atom2023Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2024Coded_nonneg g hg hA hB) (atom2025Coded_nonneg g hg hA hB)) (add_nonneg (atom2026Coded_nonneg g hg hA hB) (add_nonneg (atom2027Coded_nonneg g hg hA hB) (atom2028Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2029Coded_nonneg g hg hA hB) (atom2030Coded_nonneg g hg hA hB)) (add_nonneg (atom2031Coded_nonneg g hg hA hB) (add_nonneg (atom2032Coded_nonneg g hg hA hB) (atom2033Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2034Coded_nonneg g hg hA hB) (atom2035Coded_nonneg g hg hA hB)) (add_nonneg (atom2036Coded_nonneg g hg hA hB) (add_nonneg (atom2037Coded_nonneg g hg hA hB) (atom2038Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2039Coded_nonneg g hg hA hB) (atom2040Coded_nonneg g hg hA hB)) (add_nonneg (atom2041Coded_nonneg g hg hA hB) (add_nonneg (atom2042Coded_nonneg g hg hA hB) (atom2043Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2044Coded_nonneg g hg hA hB) (atom2045Coded_nonneg g hg hA hB)) (add_nonneg (atom2046Coded_nonneg g hg hA hB) (add_nonneg (atom2047Coded_nonneg g hg hA hB) (atom2048Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
