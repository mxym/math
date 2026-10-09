import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0976 : SparsePolynomial.Poly := [([4,7,20], 1)]
theorem eval_atom0976 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 4) * (g 7) * (g 20)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37738841800608 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976Coded : CoefficientMerge.Poly := [(1931, 1)]
theorem atom0976Coded_decode : atom0976 = SparsePolynomial.decodeCubic 21 atom0976Coded := by decide +kernel
theorem atom0976Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) := by
  have h := atom0976_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0976Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0977 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0977 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8316316713600 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977Coded : CoefficientMerge.Poly := [(1940, 1)]
theorem atom0977Coded_decode : atom0977 = SparsePolynomial.decodeCubic 21 atom0977Coded := by decide +kernel
theorem atom0977Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded) := by
  have h := atom0977_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0977Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0978 : SparsePolynomial.Poly := [([4,8,9], 1)]
theorem eval_atom0978 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14616092937600 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978Coded : CoefficientMerge.Poly := [(1941, 1)]
theorem atom0978Coded_decode : atom0978 = SparsePolynomial.decodeCubic 21 atom0978Coded := by decide +kernel
theorem atom0978Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) := by
  have h := atom0978_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0978Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0979 : SparsePolynomial.Poly := [([4,8,10], 1)]
theorem eval_atom0979 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14686645276800 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979Coded : CoefficientMerge.Poly := [(1942, 1)]
theorem atom0979Coded_decode : atom0979 = SparsePolynomial.decodeCubic 21 atom0979Coded := by decide +kernel
theorem atom0979Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) := by
  have h := atom0979_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0979Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0980 : SparsePolynomial.Poly := [([4,8,11], 1)]
theorem eval_atom0980 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14704288099200 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980Coded : CoefficientMerge.Poly := [(1943, 1)]
theorem atom0980Coded_decode : atom0980 = SparsePolynomial.decodeCubic 21 atom0980Coded := by decide +kernel
theorem atom0980Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded) := by
  have h := atom0980_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0980Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0981 : SparsePolynomial.Poly := [([4,8,12], 1)]
theorem eval_atom0981 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13399306704000 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981Coded : CoefficientMerge.Poly := [(1944, 1)]
theorem atom0981Coded_decode : atom0981 = SparsePolynomial.decodeCubic 21 atom0981Coded := by decide +kernel
theorem atom0981Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) := by
  have h := atom0981_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0981Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0982 : SparsePolynomial.Poly := [([4,8,13], 1)]
theorem eval_atom0982 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14099031273600 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982Coded : CoefficientMerge.Poly := [(1945, 1)]
theorem atom0982Coded_decode : atom0982 = SparsePolynomial.decodeCubic 21 atom0982Coded := by decide +kernel
theorem atom0982Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded) := by
  have h := atom0982_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0982Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0983 : SparsePolynomial.Poly := [([4,8,14], 1)]
theorem eval_atom0983 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14798755843200 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983Coded : CoefficientMerge.Poly := [(1946, 1)]
theorem atom0983Coded_decode : atom0983 = SparsePolynomial.decodeCubic 21 atom0983Coded := by decide +kernel
theorem atom0983Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) := by
  have h := atom0983_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0983Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0984 : SparsePolynomial.Poly := [([4,8,15], 1)]
theorem eval_atom0984 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 4) * (g 8) * (g 15)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23245546060800 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984Coded : CoefficientMerge.Poly := [(1947, 1)]
theorem atom0984Coded_decode : atom0984 = SparsePolynomial.decodeCubic 21 atom0984Coded := by decide +kernel
theorem atom0984Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) := by
  have h := atom0984_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0984Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0985 : SparsePolynomial.Poly := [([4,8,16], 1)]
theorem eval_atom0985 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 4) * (g 8) * (g 16)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20719776344400 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985Coded : CoefficientMerge.Poly := [(1948, 1)]
theorem atom0985Coded_decode : atom0985 = SparsePolynomial.decodeCubic 21 atom0985Coded := by decide +kernel
theorem atom0985Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded) := by
  have h := atom0985_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0985Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0986 : SparsePolynomial.Poly := [([4,8,17], 1)]
theorem eval_atom0986 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 4) * (g 8) * (g 17)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26086557772800 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986Coded : CoefficientMerge.Poly := [(1949, 1)]
theorem atom0986Coded_decode : atom0986 = SparsePolynomial.decodeCubic 21 atom0986Coded := by decide +kernel
theorem atom0986Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) := by
  have h := atom0986_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0986Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0987 : SparsePolynomial.Poly := [([4,8,18], 1)]
theorem eval_atom0987 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 4) * (g 8) * (g 18)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31162368207600 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987Coded : CoefficientMerge.Poly := [(1950, 1)]
theorem atom0987Coded_decode : atom0987 = SparsePolynomial.decodeCubic 21 atom0987Coded := by decide +kernel
theorem atom0987Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded) := by
  have h := atom0987_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0987Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0988 : SparsePolynomial.Poly := [([4,8,19], 1)]
theorem eval_atom0988 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 4) * (g 8) * (g 19)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37890854593200 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988Coded : CoefficientMerge.Poly := [(1951, 1)]
theorem atom0988Coded_decode : atom0988 = SparsePolynomial.decodeCubic 21 atom0988Coded := by decide +kernel
theorem atom0988Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) := by
  have h := atom0988_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0988Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0989 : SparsePolynomial.Poly := [([4,8,20], 1)]
theorem eval_atom0989 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 4) * (g 8) * (g 20)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44619340978800 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989Coded : CoefficientMerge.Poly := [(1952, 1)]
theorem atom0989Coded_decode : atom0989 = SparsePolynomial.decodeCubic 21 atom0989Coded := by decide +kernel
theorem atom0989Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) := by
  have h := atom0989_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0989Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0990 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom0990 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10739741241600 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990Coded : CoefficientMerge.Poly := [(1962, 1)]
theorem atom0990Coded_decode : atom0990 = SparsePolynomial.decodeCubic 21 atom0990Coded := by decide +kernel
theorem atom0990Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded) := by
  have h := atom0990_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0990Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0991 : SparsePolynomial.Poly := [([4,9,10], 1)]
theorem eval_atom0991 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19770762816000 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991Coded : CoefficientMerge.Poly := [(1963, 1)]
theorem atom0991Coded_decode : atom0991 = SparsePolynomial.decodeCubic 21 atom0991Coded := by decide +kernel
theorem atom0991Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) := by
  have h := atom0991_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0991Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0992 : SparsePolynomial.Poly := [([4,9,11], 1)]
theorem eval_atom0992 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19283908089600 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992Coded : CoefficientMerge.Poly := [(1964, 1)]
theorem atom0992Coded_decode : atom0992 = SparsePolynomial.decodeCubic 21 atom0992Coded := by decide +kernel
theorem atom0992Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded) := by
  have h := atom0992_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0992Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0993 : SparsePolynomial.Poly := [([4,9,12], 1)]
theorem eval_atom0993 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18160623129600 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993Coded : CoefficientMerge.Poly := [(1965, 1)]
theorem atom0993Coded_decode : atom0993 = SparsePolynomial.decodeCubic 21 atom0993Coded := by decide +kernel
theorem atom0993Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) := by
  have h := atom0993_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0993Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0994 : SparsePolynomial.Poly := [([4,9,13], 1)]
theorem eval_atom0994 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18614864217600 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994Coded : CoefficientMerge.Poly := [(1966, 1)]
theorem atom0994Coded_decode : atom0994 = SparsePolynomial.decodeCubic 21 atom0994Coded := by decide +kernel
theorem atom0994Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) := by
  have h := atom0994_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0994Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0995 : SparsePolynomial.Poly := [([4,9,14], 1)]
theorem eval_atom0995 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19069105305600 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995Coded : CoefficientMerge.Poly := [(1967, 1)]
theorem atom0995Coded_decode : atom0995 = SparsePolynomial.decodeCubic 21 atom0995Coded := by decide +kernel
theorem atom0995Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded) := by
  have h := atom0995_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0995Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0996 : SparsePolynomial.Poly := [([4,9,15], 1)]
theorem eval_atom0996 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 4) * (g 9) * (g 15)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27327917030400 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996Coded : CoefficientMerge.Poly := [(1968, 1)]
theorem atom0996Coded_decode : atom0996 = SparsePolynomial.decodeCubic 21 atom0996Coded := by decide +kernel
theorem atom0996Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) := by
  have h := atom0996_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0996Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0997 : SparsePolynomial.Poly := [([4,9,16], 1)]
theorem eval_atom0997 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 4) * (g 9) * (g 16)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24967957392000 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997Coded : CoefficientMerge.Poly := [(1969, 1)]
theorem atom0997Coded_decode : atom0997 = SparsePolynomial.decodeCubic 21 atom0997Coded := by decide +kernel
theorem atom0997Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded) := by
  have h := atom0997_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0997Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0998 : SparsePolynomial.Poly := [([4,9,17], 1)]
theorem eval_atom0998 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 4) * (g 9) * (g 17)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31850587238400 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998Coded : CoefficientMerge.Poly := [(1970, 1)]
theorem atom0998Coded_decode : atom0998 = SparsePolynomial.decodeCubic 21 atom0998Coded := by decide +kernel
theorem atom0998Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) := by
  have h := atom0998_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0998Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0999 : SparsePolynomial.Poly := [([4,9,18], 1)]
theorem eval_atom0999 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 4) * (g 9) * (g 18)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35857179388800 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999Coded : CoefficientMerge.Poly := [(1971, 1)]
theorem atom0999Coded_decode : atom0999 = SparsePolynomial.decodeCubic 21 atom0999Coded := by decide +kernel
theorem atom0999Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) := by
  have h := atom0999_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0999Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1000 : SparsePolynomial.Poly := [([4,9,19], 1)]
theorem eval_atom1000 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 4) * (g 9) * (g 19)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42965247024000 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000Coded : CoefficientMerge.Poly := [(1972, 1)]
theorem atom1000Coded_decode : atom1000 = SparsePolynomial.decodeCubic 21 atom1000Coded := by decide +kernel
theorem atom1000Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded) := by
  have h := atom1000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1001 : SparsePolynomial.Poly := [([4,9,20], 1)]
theorem eval_atom1001 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 4) * (g 9) * (g 20)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50073314659200 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001Coded : CoefficientMerge.Poly := [(1973, 1)]
theorem atom1001Coded_decode : atom1001 = SparsePolynomial.decodeCubic 21 atom1001Coded := by decide +kernel
theorem atom1001Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) := by
  have h := atom1001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1002 : SparsePolynomial.Poly := [([4,10,10], 1)]
theorem eval_atom1002 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13470986592000 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002Coded : CoefficientMerge.Poly := [(1984, 1)]
theorem atom1002Coded_decode : atom1002 = SparsePolynomial.decodeCubic 21 atom1002Coded := by decide +kernel
theorem atom1002Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded) := by
  have h := atom1002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1003 : SparsePolynomial.Poly := [([4,10,11], 1)]
theorem eval_atom1003 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25277957510400 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003Coded : CoefficientMerge.Poly := [(1985, 1)]
theorem atom1003Coded_decode : atom1003 = SparsePolynomial.decodeCubic 21 atom1003Coded := by decide +kernel
theorem atom1003Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) := by
  have h := atom1003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1004 : SparsePolynomial.Poly := [([4,10,12], 1)]
theorem eval_atom1004 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23313843302400 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004Coded : CoefficientMerge.Poly := [(1986, 1)]
theorem atom1004Coded_decode : atom1004 = SparsePolynomial.decodeCubic 21 atom1004Coded := by decide +kernel
theorem atom1004Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) := by
  have h := atom1004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1005 : SparsePolynomial.Poly := [([4,10,13], 1)]
theorem eval_atom1005 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23354435059200 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005Coded : CoefficientMerge.Poly := [(1987, 1)]
theorem atom1005Coded_decode : atom1005 = SparsePolynomial.decodeCubic 21 atom1005Coded := by decide +kernel
theorem atom1005Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded) := by
  have h := atom1005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1006 : SparsePolynomial.Poly := [([4,10,14], 1)]
theorem eval_atom1006 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23395026816000 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006Coded : CoefficientMerge.Poly := [(1988, 1)]
theorem atom1006Coded_decode : atom1006 = SparsePolynomial.decodeCubic 21 atom1006Coded := by decide +kernel
theorem atom1006Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) := by
  have h := atom1006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1007 : SparsePolynomial.Poly := [([4,10,15], 1)]
theorem eval_atom1007 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 4) * (g 10) * (g 15)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31410288000000 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007Coded : CoefficientMerge.Poly := [(1989, 1)]
theorem atom1007Coded_decode : atom1007 = SparsePolynomial.decodeCubic 21 atom1007Coded := by decide +kernel
theorem atom1007Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded) := by
  have h := atom1007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1008 : SparsePolynomial.Poly := [([4,10,16], 1)]
theorem eval_atom1008 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 4) * (g 10) * (g 16)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28735500628800 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008Coded : CoefficientMerge.Poly := [(1990, 1)]
theorem atom1008Coded_decode : atom1008 = SparsePolynomial.decodeCubic 21 atom1008Coded := by decide +kernel
theorem atom1008Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) := by
  have h := atom1008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1009 : SparsePolynomial.Poly := [([4,10,17], 1)]
theorem eval_atom1009 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 4) * (g 10) * (g 17)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37614616704000 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1009Coded : CoefficientMerge.Poly := [(1991, 1)]
theorem atom1009Coded_decode : atom1009 = SparsePolynomial.decodeCubic 21 atom1009Coded := by decide +kernel
theorem atom1009Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) := by
  have h := atom1009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1010 : SparsePolynomial.Poly := [([4,10,18], 1)]
theorem eval_atom1010 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 4) * (g 10) * (g 18)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39335264740800 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010Coded : CoefficientMerge.Poly := [(1992, 1)]
theorem atom1010Coded_decode : atom1010 = SparsePolynomial.decodeCubic 21 atom1010Coded := by decide +kernel
theorem atom1010Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded) := by
  have h := atom1010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1011 : SparsePolynomial.Poly := [([4,10,19], 1)]
theorem eval_atom1011 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 4) * (g 10) * (g 19)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46388243563200 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011Coded : CoefficientMerge.Poly := [(1993, 1)]
theorem atom1011Coded_decode : atom1011 = SparsePolynomial.decodeCubic 21 atom1011Coded := by decide +kernel
theorem atom1011Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) := by
  have h := atom1011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1012 : SparsePolynomial.Poly := [([4,10,20], 1)]
theorem eval_atom1012 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 4) * (g 10) * (g 20)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53441222385600 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012Coded : CoefficientMerge.Poly := [(1994, 1)]
theorem atom1012Coded_decode : atom1012 = SparsePolynomial.decodeCubic 21 atom1012Coded := by decide +kernel
theorem atom1012Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded) := by
  have h := atom1012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1013 : SparsePolynomial.Poly := [([4,11,11], 1)]
theorem eval_atom1013 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16246935936000 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013Coded : CoefficientMerge.Poly := [(2006, 1)]
theorem atom1013Coded_decode : atom1013 = SparsePolynomial.decodeCubic 21 atom1013Coded := by decide +kernel
theorem atom1013Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) := by
  have h := atom1013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1014 : SparsePolynomial.Poly := [([4,11,12], 1)]
theorem eval_atom1014 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28498236883200 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014Coded : CoefficientMerge.Poly := [(2007, 1)]
theorem atom1014Coded_decode : atom1014 = SparsePolynomial.decodeCubic 21 atom1014Coded := by decide +kernel
theorem atom1014Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) := by
  have h := atom1014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1015 : SparsePolynomial.Poly := [([4,11,13], 1)]
theorem eval_atom1015 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27957013459200 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015Coded : CoefficientMerge.Poly := [(2008, 1)]
theorem atom1015Coded_decode : atom1015 = SparsePolynomial.decodeCubic 21 atom1015Coded := by decide +kernel
theorem atom1015Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded) := by
  have h := atom1015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1016 : SparsePolynomial.Poly := [([4,11,14], 1)]
theorem eval_atom1016 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27415790035200 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016Coded : CoefficientMerge.Poly := [(2009, 1)]
theorem atom1016Coded_decode : atom1016 = SparsePolynomial.decodeCubic 21 atom1016Coded := by decide +kernel
theorem atom1016Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) := by
  have h := atom1016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1017 : SparsePolynomial.Poly := [([4,11,15], 1)]
theorem eval_atom1017 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 4) * (g 11) * (g 15)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34868811801600 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017Coded : CoefficientMerge.Poly := [(2010, 1)]
theorem atom1017Coded_decode : atom1017 = SparsePolynomial.decodeCubic 21 atom1017Coded := by decide +kernel
theorem atom1017Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded) := by
  have h := atom1017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1018 : SparsePolynomial.Poly := [([4,11,16], 1)]
theorem eval_atom1018 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 4) * (g 11) * (g 16)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31796949592800 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018Coded : CoefficientMerge.Poly := [(2011, 1)]
theorem atom1018Coded_decode : atom1018 = SparsePolynomial.decodeCubic 21 atom1018Coded := by decide +kernel
theorem atom1018Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) := by
  have h := atom1018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1019 : SparsePolynomial.Poly := [([4,11,17], 1)]
theorem eval_atom1019 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 4) * (g 11) * (g 17)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42754799001600 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019Coded : CoefficientMerge.Poly := [(2012, 1)]
theorem atom1019Coded_decode : atom1019 = SparsePolynomial.decodeCubic 21 atom1019Coded := by decide +kernel
theorem atom1019Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) := by
  have h := atom1019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1020 : SparsePolynomial.Poly := [([4,11,18], 1)]
theorem eval_atom1020 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 4) * (g 11) * (g 18)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41641715556000 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020Coded : CoefficientMerge.Poly := [(2013, 1)]
theorem atom1020Coded_decode : atom1020 = SparsePolynomial.decodeCubic 21 atom1020Coded := by decide +kernel
theorem atom1020Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded) := by
  have h := atom1020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1021 : SparsePolynomial.Poly := [([4,11,19], 1)]
theorem eval_atom1021 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 4) * (g 11) * (g 19)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48385300672800 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021Coded : CoefficientMerge.Poly := [(2014, 1)]
theorem atom1021Coded_decode : atom1021 = SparsePolynomial.decodeCubic 21 atom1021Coded := by decide +kernel
theorem atom1021Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) := by
  have h := atom1021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1022 : SparsePolynomial.Poly := [([4,11,20], 1)]
theorem eval_atom1022 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 4) * (g 11) * (g 20)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55128885789600 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022Coded : CoefficientMerge.Poly := [(2015, 1)]
theorem atom1022Coded_decode : atom1022 = SparsePolynomial.decodeCubic 21 atom1022Coded := by decide +kernel
theorem atom1022Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded) := by
  have h := atom1022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1023 : SparsePolynomial.Poly := [([4,12,12], 1)]
theorem eval_atom1023 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17118445881600 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023Coded : CoefficientMerge.Poly := [(2028, 1)]
theorem atom1023Coded_decode : atom1023 = SparsePolynomial.decodeCubic 21 atom1023Coded := by decide +kernel
theorem atom1023Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) := by
  have h := atom1023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1024 : SparsePolynomial.Poly := [([4,12,13], 1)]
theorem eval_atom1024 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32518507392000 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024Coded : CoefficientMerge.Poly := [(2029, 1)]
theorem atom1024Coded_decode : atom1024 = SparsePolynomial.decodeCubic 21 atom1024Coded := by decide +kernel
theorem atom1024Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) := by
  have h := atom1024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1025 : SparsePolynomial.Poly := [([4,12,14], 1)]
theorem eval_atom1025 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31227302937600 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025Coded : CoefficientMerge.Poly := [(2030, 1)]
theorem atom1025Coded_decode : atom1025 = SparsePolynomial.decodeCubic 21 atom1025Coded := by decide +kernel
theorem atom1025Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded) := by
  have h := atom1025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1026 : SparsePolynomial.Poly := [([4,12,15], 1)]
theorem eval_atom1026 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 4) * (g 12) * (g 15)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34633735248000 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026Coded : CoefficientMerge.Poly := [(2031, 1)]
theorem atom1026Coded_decode : atom1026 = SparsePolynomial.decodeCubic 21 atom1026Coded := by decide +kernel
theorem atom1026Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) := by
  have h := atom1026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1027 : SparsePolynomial.Poly := [([4,12,16], 1)]
theorem eval_atom1027 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 4) * (g 12) * (g 16)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33705364364000 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027Coded : CoefficientMerge.Poly := [(2032, 1)]
theorem atom1027Coded_decode : atom1027 = SparsePolynomial.decodeCubic 21 atom1027Coded := by decide +kernel
theorem atom1027Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded) := by
  have h := atom1027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1028 : SparsePolynomial.Poly := [([4,12,17], 1)]
theorem eval_atom1028 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 4) * (g 12) * (g 17)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43390369097600 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028Coded : CoefficientMerge.Poly := [(2033, 1)]
theorem atom1028Coded_decode : atom1028 = SparsePolynomial.decodeCubic 21 atom1028Coded := by decide +kernel
theorem atom1028Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) := by
  have h := atom1028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1029 : SparsePolynomial.Poly := [([4,12,18], 1)]
theorem eval_atom1029 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 4) * (g 12) * (g 18)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42915361938400 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029Coded : CoefficientMerge.Poly := [(2034, 1)]
theorem atom1029Coded_decode : atom1029 = SparsePolynomial.decodeCubic 21 atom1029Coded := by decide +kernel
theorem atom1029Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) := by
  have h := atom1029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1030 : SparsePolynomial.Poly := [([4,12,19], 1)]
theorem eval_atom1030 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 4) * (g 12) * (g 19)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48592346426400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030Coded : CoefficientMerge.Poly := [(2035, 1)]
theorem atom1030Coded_decode : atom1030 = SparsePolynomial.decodeCubic 21 atom1030Coded := by decide +kernel
theorem atom1030Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded) := by
  have h := atom1030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1031 : SparsePolynomial.Poly := [([4,12,20], 1)]
theorem eval_atom1031 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 4) * (g 12) * (g 20)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55028408400000 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031Coded : CoefficientMerge.Poly := [(2036, 1)]
theorem atom1031Coded_decode : atom1031 = SparsePolynomial.decodeCubic 21 atom1031Coded := by decide +kernel
theorem atom1031Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) := by
  have h := atom1031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1032 : SparsePolynomial.Poly := [([4,13,13], 1)]
theorem eval_atom1032 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19975700563200 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032Coded : CoefficientMerge.Poly := [(2050, 1)]
theorem atom1032Coded_decode : atom1032 = SparsePolynomial.decodeCubic 21 atom1032Coded := by decide +kernel
theorem atom1032Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded) := by
  have h := atom1032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1033 : SparsePolynomial.Poly := [([4,13,14], 1)]
theorem eval_atom1033 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36571516070400 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033Coded : CoefficientMerge.Poly := [(2051, 1)]
theorem atom1033Coded_decode : atom1033 = SparsePolynomial.decodeCubic 21 atom1033Coded := by decide +kernel
theorem atom1033Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) := by
  have h := atom1033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1034 : SparsePolynomial.Poly := [([4,13,15], 1)]
theorem eval_atom1034 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 4) * (g 13) * (g 15)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38601069393600 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034Coded : CoefficientMerge.Poly := [(2052, 1)]
theorem atom1034Coded_decode : atom1034 = SparsePolynomial.decodeCubic 21 atom1034Coded := by decide +kernel
theorem atom1034Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) := by
  have h := atom1034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1035 : SparsePolynomial.Poly := [([4,13,16], 1)]
theorem eval_atom1035 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 4) * (g 13) * (g 16)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36159816938400 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035Coded : CoefficientMerge.Poly := [(2053, 1)]
theorem atom1035Coded_decode : atom1035 = SparsePolynomial.decodeCubic 21 atom1035Coded := by decide +kernel
theorem atom1035Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded) := by
  have h := atom1035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1036 : SparsePolynomial.Poly := [([4,13,17], 1)]
theorem eval_atom1036 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 4) * (g 13) * (g 17)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47594873289600 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036Coded : CoefficientMerge.Poly := [(2054, 1)]
theorem atom1036Coded_decode : atom1036 = SparsePolynomial.decodeCubic 21 atom1036Coded := by decide +kernel
theorem atom1036Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) := by
  have h := atom1036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1037 : SparsePolynomial.Poly := [([4,13,18], 1)]
theorem eval_atom1037 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 4) * (g 13) * (g 18)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47799330616800 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037Coded : CoefficientMerge.Poly := [(2055, 1)]
theorem atom1037Coded_decode : atom1037 = SparsePolynomial.decodeCubic 21 atom1037Coded := by decide +kernel
theorem atom1037Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded) := by
  have h := atom1037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1038 : SparsePolynomial.Poly := [([4,13,19], 1)]
theorem eval_atom1038 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 4) * (g 13) * (g 19)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46286873474400 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038Coded : CoefficientMerge.Poly := [(2056, 1)]
theorem atom1038Coded_decode : atom1038 = SparsePolynomial.decodeCubic 21 atom1038Coded := by decide +kernel
theorem atom1038Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) := by
  have h := atom1038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1039 : SparsePolynomial.Poly := [([4,13,20], 1)]
theorem eval_atom1039 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 4) * (g 13) * (g 20)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58138510147200 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039Coded : CoefficientMerge.Poly := [(2057, 1)]
theorem atom1039Coded_decode : atom1039 = SparsePolynomial.decodeCubic 21 atom1039Coded := by decide +kernel
theorem atom1039Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) := by
  have h := atom1039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1040 : SparsePolynomial.Poly := [([4,14,14], 1)]
theorem eval_atom1040 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23439806611200 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040Coded : CoefficientMerge.Poly := [(2072, 1)]
theorem atom1040Coded_decode : atom1040 = SparsePolynomial.decodeCubic 21 atom1040Coded := by decide +kernel
theorem atom1040Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded) := by
  have h := atom1040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1041 : SparsePolynomial.Poly := [([4,14,15], 1)]
theorem eval_atom1041 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 4) * (g 14) * (g 15)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42456561436800 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041Coded : CoefficientMerge.Poly := [(2073, 1)]
theorem atom1041Coded_decode : atom1041 = SparsePolynomial.decodeCubic 21 atom1041Coded := by decide +kernel
theorem atom1041Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) := by
  have h := atom1041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1042 : SparsePolynomial.Poly := [([4,14,16], 1)]
theorem eval_atom1042 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 4) * (g 14) * (g 16)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38495120076000 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042Coded : CoefficientMerge.Poly := [(2074, 1)]
theorem atom1042Coded_decode : atom1042 = SparsePolynomial.decodeCubic 21 atom1042Coded := by decide +kernel
theorem atom1042Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded) := by
  have h := atom1042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1043 : SparsePolynomial.Poly := [([4,14,17], 1)]
theorem eval_atom1043 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 4) * (g 14) * (g 17)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53992907337600 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043Coded : CoefficientMerge.Poly := [(2075, 1)]
theorem atom1043Coded_decode : atom1043 = SparsePolynomial.decodeCubic 21 atom1043Coded := by decide +kernel
theorem atom1043Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) := by
  have h := atom1043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1044 : SparsePolynomial.Poly := [([4,14,18], 1)]
theorem eval_atom1044 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 4) * (g 14) * (g 18)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55096182136800 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044Coded : CoefficientMerge.Poly := [(2076, 1)]
theorem atom1044Coded_decode : atom1044 = SparsePolynomial.decodeCubic 21 atom1044Coded := by decide +kernel
theorem atom1044Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) := by
  have h := atom1044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1045 : SparsePolynomial.Poly := [([4,14,19], 1)]
theorem eval_atom1045 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 4) * (g 14) * (g 19)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48432127111200 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045Coded : CoefficientMerge.Poly := [(2077, 1)]
theorem atom1045Coded_decode : atom1045 = SparsePolynomial.decodeCubic 21 atom1045Coded := by decide +kernel
theorem atom1045Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded) := by
  have h := atom1045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1046 : SparsePolynomial.Poly := [([4,14,20], 1)]
theorem eval_atom1046 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 4) * (g 14) * (g 20)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65831614531200 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046Coded : CoefficientMerge.Poly := [(2078, 1)]
theorem atom1046Coded_decode : atom1046 = SparsePolynomial.decodeCubic 21 atom1046Coded := by decide +kernel
theorem atom1046Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) := by
  have h := atom1046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1047 : SparsePolynomial.Poly := [([4,15,15], 1)]
theorem eval_atom1047 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27544406400000 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047Coded : CoefficientMerge.Poly := [(2094, 1)]
theorem atom1047Coded_decode : atom1047 = SparsePolynomial.decodeCubic 21 atom1047Coded := by decide +kernel
theorem atom1047Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded) := by
  have h := atom1047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1048 : SparsePolynomial.Poly := [([4,15,16], 1)]
theorem eval_atom1048 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49565736486000 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048Coded : CoefficientMerge.Poly := [(2095, 1)]
theorem atom1048Coded_decode : atom1048 = SparsePolynomial.decodeCubic 21 atom1048Coded := by decide +kernel
theorem atom1048Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) := by
  have h := atom1048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1049 : SparsePolynomial.Poly := [([4,15,17], 1)]
theorem eval_atom1049 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69701433984000 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049Coded : CoefficientMerge.Poly := [(2096, 1)]
theorem atom1049Coded_decode : atom1049 = SparsePolynomial.decodeCubic 21 atom1049Coded := by decide +kernel
theorem atom1049Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) := by
  have h := atom1049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1050 : SparsePolynomial.Poly := [([4,15,18], 1)]
theorem eval_atom1050 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 4) * (g 15) * (g 18)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67506930565200 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050Coded : CoefficientMerge.Poly := [(2097, 1)]
theorem atom1050Coded_decode : atom1050 = SparsePolynomial.decodeCubic 21 atom1050Coded := by decide +kernel
theorem atom1050Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded) := by
  have h := atom1050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1051 : SparsePolynomial.Poly := [([4,15,19], 1)]
theorem eval_atom1051 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 4) * (g 15) * (g 19)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46776865338000 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051Coded : CoefficientMerge.Poly := [(2098, 1)]
theorem atom1051Coded_decode : atom1051 = SparsePolynomial.decodeCubic 21 atom1051Coded := by decide +kernel
theorem atom1051Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) := by
  have h := atom1051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1052 : SparsePolynomial.Poly := [([4,15,20], 1)]
theorem eval_atom1052 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 4) * (g 15) * (g 20)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68668144750800 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052Coded : CoefficientMerge.Poly := [(2099, 1)]
theorem atom1052Coded_decode : atom1052 = SparsePolynomial.decodeCubic 21 atom1052Coded := by decide +kernel
theorem atom1052Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded) := by
  have h := atom1052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1053 : SparsePolynomial.Poly := [([4,16,16], 1)]
theorem eval_atom1053 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 4) * (g 16) * (g 16)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19150031093760 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053Coded : CoefficientMerge.Poly := [(2116, 1)]
theorem atom1053Coded_decode : atom1053 = SparsePolynomial.decodeCubic 21 atom1053Coded := by decide +kernel
theorem atom1053Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) := by
  have h := atom1053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1054 : SparsePolynomial.Poly := [([4,16,17], 1)]
theorem eval_atom1054 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54894908250000 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054Coded : CoefficientMerge.Poly := [(2117, 1)]
theorem atom1054Coded_decode : atom1054 = SparsePolynomial.decodeCubic 21 atom1054Coded := by decide +kernel
theorem atom1054Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) := by
  have h := atom1054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1055 : SparsePolynomial.Poly := [([4,16,18], 1)]
theorem eval_atom1055 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1055 = ((g 4) * (g 16) * (g 18)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1055_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55511190567000 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1055Coded : CoefficientMerge.Poly := [(2118, 1)]
theorem atom1055Coded_decode : atom1055 = SparsePolynomial.decodeCubic 21 atom1055Coded := by decide +kernel
theorem atom1055Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded) := by
  have h := atom1055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block014 : CoefficientMerge.Poly := [(1931, 37738841800608), (1940, 8316316713600), (1941, 14616092937600), (1942, 14686645276800), (1943, 14704288099200), (1944, 13399306704000), (1945, 14099031273600), (1946, 14798755843200), (1947, 23245546060800), (1948, 20719776344400), (1949, 26086557772800), (1950, 31162368207600), (1951, 37890854593200), (1952, 44619340978800), (1962, 10739741241600), (1963, 19770762816000), (1964, 19283908089600), (1965, 18160623129600), (1966, 18614864217600), (1967, 19069105305600), (1968, 27327917030400), (1969, 24967957392000), (1970, 31850587238400), (1971, 35857179388800), (1972, 42965247024000), (1973, 50073314659200), (1984, 13470986592000), (1985, 25277957510400), (1986, 23313843302400), (1987, 23354435059200), (1988, 23395026816000), (1989, 31410288000000), (1990, 28735500628800), (1991, 37614616704000), (1992, 39335264740800), (1993, 46388243563200), (1994, 53441222385600), (2006, 16246935936000), (2007, 28498236883200), (2008, 27957013459200), (2009, 27415790035200), (2010, 34868811801600), (2011, 31796949592800), (2012, 42754799001600), (2013, 41641715556000), (2014, 48385300672800), (2015, 55128885789600), (2028, 17118445881600), (2029, 32518507392000), (2030, 31227302937600), (2031, 34633735248000), (2032, 33705364364000), (2033, 43390369097600), (2034, 42915361938400), (2035, 48592346426400), (2036, 55028408400000), (2050, 19975700563200), (2051, 36571516070400), (2052, 38601069393600), (2053, 36159816938400), (2054, 47594873289600), (2055, 47799330616800), (2056, 46286873474400), (2057, 58138510147200), (2072, 23439806611200), (2073, 42456561436800), (2074, 38495120076000), (2075, 53992907337600), (2076, 55096182136800), (2077, 48432127111200), (2078, 65831614531200), (2094, 27544406400000), (2095, 49565736486000), (2096, 69701433984000), (2097, 67506930565200), (2098, 46776865338000), (2099, 68668144750800), (2116, 19150031093760), (2117, 54894908250000), (2118, 55511190567000)]
theorem block014_data : block014 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37738841800608 : Int) atom0976Coded) (CoefficientMerge.scale (8316316713600 : Int) atom0977Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14616092937600 : Int) atom0978Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14686645276800 : Int) atom0979Coded) (CoefficientMerge.scale (14704288099200 : Int) atom0980Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13399306704000 : Int) atom0981Coded) (CoefficientMerge.scale (14099031273600 : Int) atom0982Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14798755843200 : Int) atom0983Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23245546060800 : Int) atom0984Coded) (CoefficientMerge.scale (20719776344400 : Int) atom0985Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26086557772800 : Int) atom0986Coded) (CoefficientMerge.scale (31162368207600 : Int) atom0987Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37890854593200 : Int) atom0988Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44619340978800 : Int) atom0989Coded) (CoefficientMerge.scale (10739741241600 : Int) atom0990Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19770762816000 : Int) atom0991Coded) (CoefficientMerge.scale (19283908089600 : Int) atom0992Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18160623129600 : Int) atom0993Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18614864217600 : Int) atom0994Coded) (CoefficientMerge.scale (19069105305600 : Int) atom0995Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27327917030400 : Int) atom0996Coded) (CoefficientMerge.scale (24967957392000 : Int) atom0997Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31850587238400 : Int) atom0998Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35857179388800 : Int) atom0999Coded) (CoefficientMerge.scale (42965247024000 : Int) atom1000Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50073314659200 : Int) atom1001Coded) (CoefficientMerge.scale (13470986592000 : Int) atom1002Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25277957510400 : Int) atom1003Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23313843302400 : Int) atom1004Coded) (CoefficientMerge.scale (23354435059200 : Int) atom1005Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23395026816000 : Int) atom1006Coded) (CoefficientMerge.scale (31410288000000 : Int) atom1007Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28735500628800 : Int) atom1008Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37614616704000 : Int) atom1009Coded) (CoefficientMerge.scale (39335264740800 : Int) atom1010Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46388243563200 : Int) atom1011Coded) (CoefficientMerge.scale (53441222385600 : Int) atom1012Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16246935936000 : Int) atom1013Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28498236883200 : Int) atom1014Coded) (CoefficientMerge.scale (27957013459200 : Int) atom1015Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27415790035200 : Int) atom1016Coded) (CoefficientMerge.scale (34868811801600 : Int) atom1017Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31796949592800 : Int) atom1018Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42754799001600 : Int) atom1019Coded) (CoefficientMerge.scale (41641715556000 : Int) atom1020Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48385300672800 : Int) atom1021Coded) (CoefficientMerge.scale (55128885789600 : Int) atom1022Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17118445881600 : Int) atom1023Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32518507392000 : Int) atom1024Coded) (CoefficientMerge.scale (31227302937600 : Int) atom1025Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34633735248000 : Int) atom1026Coded) (CoefficientMerge.scale (33705364364000 : Int) atom1027Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43390369097600 : Int) atom1028Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42915361938400 : Int) atom1029Coded) (CoefficientMerge.scale (48592346426400 : Int) atom1030Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55028408400000 : Int) atom1031Coded) (CoefficientMerge.scale (19975700563200 : Int) atom1032Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36571516070400 : Int) atom1033Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38601069393600 : Int) atom1034Coded) (CoefficientMerge.scale (36159816938400 : Int) atom1035Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47594873289600 : Int) atom1036Coded) (CoefficientMerge.scale (47799330616800 : Int) atom1037Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46286873474400 : Int) atom1038Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58138510147200 : Int) atom1039Coded) (CoefficientMerge.scale (23439806611200 : Int) atom1040Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42456561436800 : Int) atom1041Coded) (CoefficientMerge.scale (38495120076000 : Int) atom1042Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53992907337600 : Int) atom1043Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55096182136800 : Int) atom1044Coded) (CoefficientMerge.scale (48432127111200 : Int) atom1045Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65831614531200 : Int) atom1046Coded) (CoefficientMerge.scale (27544406400000 : Int) atom1047Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49565736486000 : Int) atom1048Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69701433984000 : Int) atom1049Coded) (CoefficientMerge.scale (67506930565200 : Int) atom1050Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46776865338000 : Int) atom1051Coded) (CoefficientMerge.scale (68668144750800 : Int) atom1052Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19150031093760 : Int) atom1053Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54894908250000 : Int) atom1054Coded) (CoefficientMerge.scale (55511190567000 : Int) atom1055Coded)))))))) := by decide +kernel
theorem block014_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block014 := by
  rw [block014_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0976Coded_nonneg g hg hA hB) (atom0977Coded_nonneg g hg hA hB)) (add_nonneg (atom0978Coded_nonneg g hg hA hB) (add_nonneg (atom0979Coded_nonneg g hg hA hB) (atom0980Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0981Coded_nonneg g hg hA hB) (atom0982Coded_nonneg g hg hA hB)) (add_nonneg (atom0983Coded_nonneg g hg hA hB) (add_nonneg (atom0984Coded_nonneg g hg hA hB) (atom0985Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0986Coded_nonneg g hg hA hB) (atom0987Coded_nonneg g hg hA hB)) (add_nonneg (atom0988Coded_nonneg g hg hA hB) (add_nonneg (atom0989Coded_nonneg g hg hA hB) (atom0990Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0991Coded_nonneg g hg hA hB) (atom0992Coded_nonneg g hg hA hB)) (add_nonneg (atom0993Coded_nonneg g hg hA hB) (add_nonneg (atom0994Coded_nonneg g hg hA hB) (atom0995Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0996Coded_nonneg g hg hA hB) (atom0997Coded_nonneg g hg hA hB)) (add_nonneg (atom0998Coded_nonneg g hg hA hB) (add_nonneg (atom0999Coded_nonneg g hg hA hB) (atom1000Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1001Coded_nonneg g hg hA hB) (atom1002Coded_nonneg g hg hA hB)) (add_nonneg (atom1003Coded_nonneg g hg hA hB) (add_nonneg (atom1004Coded_nonneg g hg hA hB) (atom1005Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1006Coded_nonneg g hg hA hB) (atom1007Coded_nonneg g hg hA hB)) (add_nonneg (atom1008Coded_nonneg g hg hA hB) (add_nonneg (atom1009Coded_nonneg g hg hA hB) (atom1010Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1011Coded_nonneg g hg hA hB) (atom1012Coded_nonneg g hg hA hB)) (add_nonneg (atom1013Coded_nonneg g hg hA hB) (add_nonneg (atom1014Coded_nonneg g hg hA hB) (atom1015Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1016Coded_nonneg g hg hA hB) (atom1017Coded_nonneg g hg hA hB)) (add_nonneg (atom1018Coded_nonneg g hg hA hB) (add_nonneg (atom1019Coded_nonneg g hg hA hB) (atom1020Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1021Coded_nonneg g hg hA hB) (atom1022Coded_nonneg g hg hA hB)) (add_nonneg (atom1023Coded_nonneg g hg hA hB) (add_nonneg (atom1024Coded_nonneg g hg hA hB) (atom1025Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1026Coded_nonneg g hg hA hB) (atom1027Coded_nonneg g hg hA hB)) (add_nonneg (atom1028Coded_nonneg g hg hA hB) (add_nonneg (atom1029Coded_nonneg g hg hA hB) (atom1030Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1031Coded_nonneg g hg hA hB) (atom1032Coded_nonneg g hg hA hB)) (add_nonneg (atom1033Coded_nonneg g hg hA hB) (add_nonneg (atom1034Coded_nonneg g hg hA hB) (atom1035Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1036Coded_nonneg g hg hA hB) (atom1037Coded_nonneg g hg hA hB)) (add_nonneg (atom1038Coded_nonneg g hg hA hB) (add_nonneg (atom1039Coded_nonneg g hg hA hB) (atom1040Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1041Coded_nonneg g hg hA hB) (atom1042Coded_nonneg g hg hA hB)) (add_nonneg (atom1043Coded_nonneg g hg hA hB) (add_nonneg (atom1044Coded_nonneg g hg hA hB) (atom1045Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1046Coded_nonneg g hg hA hB) (atom1047Coded_nonneg g hg hA hB)) (add_nonneg (atom1048Coded_nonneg g hg hA hB) (add_nonneg (atom1049Coded_nonneg g hg hA hB) (atom1050Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1051Coded_nonneg g hg hA hB) (atom1052Coded_nonneg g hg hA hB)) (add_nonneg (atom1053Coded_nonneg g hg hA hB) (add_nonneg (atom1054Coded_nonneg g hg hA hB) (atom1055Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
