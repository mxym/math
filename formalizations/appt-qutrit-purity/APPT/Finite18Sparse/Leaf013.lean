import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0975 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom0975 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1914984960 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0975Coded : CoefficientMerge.Poly := [(2820, 1)]
theorem atom0975Coded_decode : atom0975 = SparsePolynomial.decodeCubic 18 atom0975Coded := by decide +kernel
theorem atom0975Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1914984960 : Int) atom0975Coded) := by
  have h := atom0975_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0975Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0976 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom0976 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4619473920 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976Coded : CoefficientMerge.Poly := [(2821, 1)]
theorem atom0976Coded_decode : atom0976 = SparsePolynomial.decodeCubic 18 atom0976Coded := by decide +kernel
theorem atom0976Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4619473920 : Int) atom0976Coded) := by
  have h := atom0976_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0976Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0977 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom0977 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10744620960 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977Coded : CoefficientMerge.Poly := [(2822, 1)]
theorem atom0977Coded_decode : atom0977 = SparsePolynomial.decodeCubic 18 atom0977Coded := by decide +kernel
theorem atom0977Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10744620960 : Int) atom0977Coded) := by
  have h := atom0977_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0977Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0978 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom0978 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11856384000 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978Coded : CoefficientMerge.Poly := [(2823, 1)]
theorem atom0978Coded_decode : atom0978 = SparsePolynomial.decodeCubic 18 atom0978Coded := by decide +kernel
theorem atom0978Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11856384000 : Int) atom0978Coded) := by
  have h := atom0978_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0978Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0979 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom0979 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9369254400 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979Coded : CoefficientMerge.Poly := [(2824, 1)]
theorem atom0979Coded_decode : atom0979 = SparsePolynomial.decodeCubic 18 atom0979Coded := by decide +kernel
theorem atom0979Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9369254400 : Int) atom0979Coded) := by
  have h := atom0979_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0979Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0980 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom0980 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15816660480 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980Coded : CoefficientMerge.Poly := [(2825, 1)]
theorem atom0980Coded_decode : atom0980 = SparsePolynomial.decodeCubic 18 atom0980Coded := by decide +kernel
theorem atom0980Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15816660480 : Int) atom0980Coded) := by
  have h := atom0980_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0980Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0981 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom0981 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1790734848 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981Coded : CoefficientMerge.Poly := [(2839, 1)]
theorem atom0981Coded_decode : atom0981 = SparsePolynomial.decodeCubic 18 atom0981Coded := by decide +kernel
theorem atom0981Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1790734848 : Int) atom0981Coded) := by
  have h := atom0981_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0981Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0982 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom0982 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8615461560 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982Coded : CoefficientMerge.Poly := [(2840, 1)]
theorem atom0982Coded_decode : atom0982 = SparsePolynomial.decodeCubic 18 atom0982Coded := by decide +kernel
theorem atom0982Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8615461560 : Int) atom0982Coded) := by
  have h := atom0982_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0982Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0983 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom0983 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10629073920 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983Coded : CoefficientMerge.Poly := [(2841, 1)]
theorem atom0983Coded_decode : atom0983 = SparsePolynomial.decodeCubic 18 atom0983Coded := by decide +kernel
theorem atom0983Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10629073920 : Int) atom0983Coded) := by
  have h := atom0983_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0983Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0984 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom0984 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8825487360 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984Coded : CoefficientMerge.Poly := [(2842, 1)]
theorem atom0984Coded_decode : atom0984 = SparsePolynomial.decodeCubic 18 atom0984Coded := by decide +kernel
theorem atom0984Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8825487360 : Int) atom0984Coded) := by
  have h := atom0984_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0984Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0985 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom0985 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12648821760 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985Coded : CoefficientMerge.Poly := [(2843, 1)]
theorem atom0985Coded_decode : atom0985 = SparsePolynomial.decodeCubic 18 atom0985Coded := by decide +kernel
theorem atom0985Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12648821760 : Int) atom0985Coded) := by
  have h := atom0985_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0985Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0986 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom0986 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7466756280 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986Coded : CoefficientMerge.Poly := [(2858, 1)]
theorem atom0986Coded_decode : atom0986 = SparsePolynomial.decodeCubic 18 atom0986Coded := by decide +kernel
theorem atom0986Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7466756280 : Int) atom0986Coded) := by
  have h := atom0986_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0986Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0987 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom0987 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13350688440 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987Coded : CoefficientMerge.Poly := [(2859, 1)]
theorem atom0987Coded_decode : atom0987 = SparsePolynomial.decodeCubic 18 atom0987Coded := by decide +kernel
theorem atom0987Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13350688440 : Int) atom0987Coded) := by
  have h := atom0987_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0987Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0988 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom0988 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11285680080 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988Coded : CoefficientMerge.Poly := [(2860, 1)]
theorem atom0988Coded_decode : atom0988 = SparsePolynomial.decodeCubic 18 atom0988Coded := by decide +kernel
theorem atom0988Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11285680080 : Int) atom0988Coded) := by
  have h := atom0988_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0988Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0989 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom0989 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16222276560 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989Coded : CoefficientMerge.Poly := [(2861, 1)]
theorem atom0989Coded_decode : atom0989 = SparsePolynomial.decodeCubic 18 atom0989Coded := by decide +kernel
theorem atom0989Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16222276560 : Int) atom0989Coded) := by
  have h := atom0989_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0989Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0990 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom0990 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4506685440 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990Coded : CoefficientMerge.Poly := [(2877, 1)]
theorem atom0990Coded_decode : atom0990 = SparsePolynomial.decodeCubic 18 atom0990Coded := by decide +kernel
theorem atom0990Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4506685440 : Int) atom0990Coded) := by
  have h := atom0990_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0990Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0991 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom0991 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8103102720 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991Coded : CoefficientMerge.Poly := [(2878, 1)]
theorem atom0991Coded_decode : atom0991 = SparsePolynomial.decodeCubic 18 atom0991Coded := by decide +kernel
theorem atom0991Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8103102720 : Int) atom0991Coded) := by
  have h := atom0991_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0991Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0992 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom0992 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13606763520 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992Coded : CoefficientMerge.Poly := [(2879, 1)]
theorem atom0992Coded_decode : atom0992 = SparsePolynomial.decodeCubic 18 atom0992Coded := by decide +kernel
theorem atom0992Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13606763520 : Int) atom0992Coded) := by
  have h := atom0992_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0992Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0993 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom0993 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2134348800 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993Coded : CoefficientMerge.Poly := [(2896, 1)]
theorem atom0993Coded_decode : atom0993 = SparsePolynomial.decodeCubic 18 atom0993Coded := by decide +kernel
theorem atom0993Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2134348800 : Int) atom0993Coded) := by
  have h := atom0993_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0993Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0994 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom0994 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10271395200 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994Coded : CoefficientMerge.Poly := [(2897, 1)]
theorem atom0994Coded_decode : atom0994 = SparsePolynomial.decodeCubic 18 atom0994Coded := by decide +kernel
theorem atom0994Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10271395200 : Int) atom0994Coded) := by
  have h := atom0994_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0994Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0995 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom0995 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7369979520 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995Coded : CoefficientMerge.Poly := [(2915, 1)]
theorem atom0995Coded_decode : atom0995 = SparsePolynomial.decodeCubic 18 atom0995Coded := by decide +kernel
theorem atom0995Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7369979520 : Int) atom0995Coded) := by
  have h := atom0995_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0995Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0996 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom0996 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116904960 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996Coded : CoefficientMerge.Poly := [(3087, 1)]
theorem atom0996Coded_decode : atom0996 = SparsePolynomial.decodeCubic 18 atom0996Coded := by decide +kernel
theorem atom0996Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (116904960 : Int) atom0996Coded) := by
  have h := atom0996_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0996Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0997 : SparsePolynomial.Poly := [([9,9,14], 1)]
theorem eval_atom0997 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 9) * (g 9) * (g 14)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16292880 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997Coded : CoefficientMerge.Poly := [(3092, 1)]
theorem atom0997Coded_decode : atom0997 = SparsePolynomial.decodeCubic 18 atom0997Coded := by decide +kernel
theorem atom0997Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16292880 : Int) atom0997Coded) := by
  have h := atom0997_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0997Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0998 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom0998 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115061760 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998Coded : CoefficientMerge.Poly := [(3106, 1)]
theorem atom0998Coded_decode : atom0998 = SparsePolynomial.decodeCubic 18 atom0998Coded := by decide +kernel
theorem atom0998Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (115061760 : Int) atom0998Coded) := by
  have h := atom0998_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0998Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0999 : SparsePolynomial.Poly := [([9,10,13], 1)]
theorem eval_atom0999 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (285358080 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999Coded : CoefficientMerge.Poly := [(3109, 1)]
theorem atom0999Coded_decode : atom0999 = SparsePolynomial.decodeCubic 18 atom0999Coded := by decide +kernel
theorem atom0999Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (285358080 : Int) atom0999Coded) := by
  have h := atom0999_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0999Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1000 : SparsePolynomial.Poly := [([9,10,14], 1)]
theorem eval_atom1000 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1766186400 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000Coded : CoefficientMerge.Poly := [(3110, 1)]
theorem atom1000Coded_decode : atom1000 = SparsePolynomial.decodeCubic 18 atom1000Coded := by decide +kernel
theorem atom1000Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1766186400 : Int) atom1000Coded) := by
  have h := atom1000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1001 : SparsePolynomial.Poly := [([9,10,15], 1)]
theorem eval_atom1001 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1621401600 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001Coded : CoefficientMerge.Poly := [(3111, 1)]
theorem atom1001Coded_decode : atom1001 = SparsePolynomial.decodeCubic 18 atom1001Coded := by decide +kernel
theorem atom1001Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1621401600 : Int) atom1001Coded) := by
  have h := atom1001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1002 : SparsePolynomial.Poly := [([9,10,16], 1)]
theorem eval_atom1002 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 9) * (g 10) * (g 16)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2672087040 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002Coded : CoefficientMerge.Poly := [(3112, 1)]
theorem atom1002Coded_decode : atom1002 = SparsePolynomial.decodeCubic 18 atom1002Coded := by decide +kernel
theorem atom1002Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2672087040 : Int) atom1002Coded) := by
  have h := atom1002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1003 : SparsePolynomial.Poly := [([9,10,17], 1)]
theorem eval_atom1003 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4110834240 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003Coded : CoefficientMerge.Poly := [(3113, 1)]
theorem atom1003Coded_decode : atom1003 = SparsePolynomial.decodeCubic 18 atom1003Coded := by decide +kernel
theorem atom1003Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4110834240 : Int) atom1003Coded) := by
  have h := atom1003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1004 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom1004 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (684334080 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004Coded : CoefficientMerge.Poly := [(3125, 1)]
theorem atom1004Coded_decode : atom1004 = SparsePolynomial.decodeCubic 18 atom1004Coded := by decide +kernel
theorem atom1004Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (684334080 : Int) atom1004Coded) := by
  have h := atom1004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1005 : SparsePolynomial.Poly := [([9,11,13], 1)]
theorem eval_atom1005 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (279352320 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005Coded : CoefficientMerge.Poly := [(3127, 1)]
theorem atom1005Coded_decode : atom1005 = SparsePolynomial.decodeCubic 18 atom1005Coded := by decide +kernel
theorem atom1005Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (279352320 : Int) atom1005Coded) := by
  have h := atom1005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1006 : SparsePolynomial.Poly := [([9,11,14], 1)]
theorem eval_atom1006 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3051218400 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006Coded : CoefficientMerge.Poly := [(3128, 1)]
theorem atom1006Coded_decode : atom1006 = SparsePolynomial.decodeCubic 18 atom1006Coded := by decide +kernel
theorem atom1006Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3051218400 : Int) atom1006Coded) := by
  have h := atom1006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1007 : SparsePolynomial.Poly := [([9,11,15], 1)]
theorem eval_atom1007 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3584509440 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007Coded : CoefficientMerge.Poly := [(3129, 1)]
theorem atom1007Coded_decode : atom1007 = SparsePolynomial.decodeCubic 18 atom1007Coded := by decide +kernel
theorem atom1007Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3584509440 : Int) atom1007Coded) := by
  have h := atom1007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1008 : SparsePolynomial.Poly := [([9,11,16], 1)]
theorem eval_atom1008 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4543349760 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008Coded : CoefficientMerge.Poly := [(3130, 1)]
theorem atom1008Coded_decode : atom1008 = SparsePolynomial.decodeCubic 18 atom1008Coded := by decide +kernel
theorem atom1008Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4543349760 : Int) atom1008Coded) := by
  have h := atom1008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1009 : SparsePolynomial.Poly := [([9,11,17], 1)]
theorem eval_atom1009 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9320682240 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1009Coded : CoefficientMerge.Poly := [(3131, 1)]
theorem atom1009Coded_decode : atom1009 = SparsePolynomial.decodeCubic 18 atom1009Coded := by decide +kernel
theorem atom1009Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9320682240 : Int) atom1009Coded) := by
  have h := atom1009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1010 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom1010 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1234574880 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010Coded : CoefficientMerge.Poly := [(3144, 1)]
theorem atom1010Coded_decode : atom1010 = SparsePolynomial.decodeCubic 18 atom1010Coded := by decide +kernel
theorem atom1010Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1234574880 : Int) atom1010Coded) := by
  have h := atom1010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1011 : SparsePolynomial.Poly := [([9,12,13], 1)]
theorem eval_atom1011 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3395495520 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011Coded : CoefficientMerge.Poly := [(3145, 1)]
theorem atom1011Coded_decode : atom1011 = SparsePolynomial.decodeCubic 18 atom1011Coded := by decide +kernel
theorem atom1011Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3395495520 : Int) atom1011Coded) := by
  have h := atom1011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1012 : SparsePolynomial.Poly := [([9,12,14], 1)]
theorem eval_atom1012 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9850293120 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012Coded : CoefficientMerge.Poly := [(3146, 1)]
theorem atom1012Coded_decode : atom1012 = SparsePolynomial.decodeCubic 18 atom1012Coded := by decide +kernel
theorem atom1012Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9850293120 : Int) atom1012Coded) := by
  have h := atom1012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1013 : SparsePolynomial.Poly := [([9,12,15], 1)]
theorem eval_atom1013 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10984189680 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013Coded : CoefficientMerge.Poly := [(3147, 1)]
theorem atom1013Coded_decode : atom1013 = SparsePolynomial.decodeCubic 18 atom1013Coded := by decide +kernel
theorem atom1013Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10984189680 : Int) atom1013Coded) := by
  have h := atom1013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1014 : SparsePolynomial.Poly := [([9,12,16], 1)]
theorem eval_atom1014 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8721034080 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014Coded : CoefficientMerge.Poly := [(3148, 1)]
theorem atom1014Coded_decode : atom1014 = SparsePolynomial.decodeCubic 18 atom1014Coded := by decide +kernel
theorem atom1014Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8721034080 : Int) atom1014Coded) := by
  have h := atom1014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1015 : SparsePolynomial.Poly := [([9,12,17], 1)]
theorem eval_atom1015 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15410525400 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015Coded : CoefficientMerge.Poly := [(3149, 1)]
theorem atom1015Coded_decode : atom1015 = SparsePolynomial.decodeCubic 18 atom1015Coded := by decide +kernel
theorem atom1015Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15410525400 : Int) atom1015Coded) := by
  have h := atom1015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1016 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom1016 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1293992448 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016Coded : CoefficientMerge.Poly := [(3163, 1)]
theorem atom1016Coded_decode : atom1016 = SparsePolynomial.decodeCubic 18 atom1016Coded := by decide +kernel
theorem atom1016Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1293992448 : Int) atom1016Coded) := by
  have h := atom1016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1017 : SparsePolynomial.Poly := [([9,13,14], 1)]
theorem eval_atom1017 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8110518360 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017Coded : CoefficientMerge.Poly := [(3164, 1)]
theorem atom1017Coded_decode : atom1017 = SparsePolynomial.decodeCubic 18 atom1017Coded := by decide +kernel
theorem atom1017Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8110518360 : Int) atom1017Coded) := by
  have h := atom1017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1018 : SparsePolynomial.Poly := [([9,13,15], 1)]
theorem eval_atom1018 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10591613040 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018Coded : CoefficientMerge.Poly := [(3165, 1)]
theorem atom1018Coded_decode : atom1018 = SparsePolynomial.decodeCubic 18 atom1018Coded := by decide +kernel
theorem atom1018Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10591613040 : Int) atom1018Coded) := by
  have h := atom1018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1019 : SparsePolynomial.Poly := [([9,13,16], 1)]
theorem eval_atom1019 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9273572160 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019Coded : CoefficientMerge.Poly := [(3166, 1)]
theorem atom1019Coded_decode : atom1019 = SparsePolynomial.decodeCubic 18 atom1019Coded := by decide +kernel
theorem atom1019Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9273572160 : Int) atom1019Coded) := by
  have h := atom1019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1020 : SparsePolynomial.Poly := [([9,13,17], 1)]
theorem eval_atom1020 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13553859240 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020Coded : CoefficientMerge.Poly := [(3167, 1)]
theorem atom1020Coded_decode : atom1020 = SparsePolynomial.decodeCubic 18 atom1020Coded := by decide +kernel
theorem atom1020Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13553859240 : Int) atom1020Coded) := by
  have h := atom1020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1021 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom1021 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7312572600 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021Coded : CoefficientMerge.Poly := [(3182, 1)]
theorem atom1021Coded_decode : atom1021 = SparsePolynomial.decodeCubic 18 atom1021Coded := by decide +kernel
theorem atom1021Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7312572600 : Int) atom1021Coded) := by
  have h := atom1021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1022 : SparsePolynomial.Poly := [([9,14,15], 1)]
theorem eval_atom1022 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13858747800 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022Coded : CoefficientMerge.Poly := [(3183, 1)]
theorem atom1022Coded_decode : atom1022 = SparsePolynomial.decodeCubic 18 atom1022Coded := by decide +kernel
theorem atom1022Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13858747800 : Int) atom1022Coded) := by
  have h := atom1022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1023 : SparsePolynomial.Poly := [([9,14,16], 1)]
theorem eval_atom1023 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12444452400 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023Coded : CoefficientMerge.Poly := [(3184, 1)]
theorem atom1023Coded_decode : atom1023 = SparsePolynomial.decodeCubic 18 atom1023Coded := by decide +kernel
theorem atom1023Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12444452400 : Int) atom1023Coded) := by
  have h := atom1023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1024 : SparsePolynomial.Poly := [([9,14,17], 1)]
theorem eval_atom1024 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18040793520 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024Coded : CoefficientMerge.Poly := [(3185, 1)]
theorem atom1024Coded_decode : atom1024 = SparsePolynomial.decodeCubic 18 atom1024Coded := by decide +kernel
theorem atom1024Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (18040793520 : Int) atom1024Coded) := by
  have h := atom1024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1025 : SparsePolynomial.Poly := [([9,15,15], 1)]
theorem eval_atom1025 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5224906320 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025Coded : CoefficientMerge.Poly := [(3201, 1)]
theorem atom1025Coded_decode : atom1025 = SparsePolynomial.decodeCubic 18 atom1025Coded := by decide +kernel
theorem atom1025Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5224906320 : Int) atom1025Coded) := by
  have h := atom1025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1026 : SparsePolynomial.Poly := [([9,15,16], 1)]
theorem eval_atom1026 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10468372560 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026Coded : CoefficientMerge.Poly := [(3202, 1)]
theorem atom1026Coded_decode : atom1026 = SparsePolynomial.decodeCubic 18 atom1026Coded := by decide +kernel
theorem atom1026Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10468372560 : Int) atom1026Coded) := by
  have h := atom1026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1027 : SparsePolynomial.Poly := [([9,15,17], 1)]
theorem eval_atom1027 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16825456200 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027Coded : CoefficientMerge.Poly := [(3203, 1)]
theorem atom1027Coded_decode : atom1027 = SparsePolynomial.decodeCubic 18 atom1027Coded := by decide +kernel
theorem atom1027Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16825456200 : Int) atom1027Coded) := by
  have h := atom1027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1028 : SparsePolynomial.Poly := [([9,16,16], 1)]
theorem eval_atom1028 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3736455360 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028Coded : CoefficientMerge.Poly := [(3220, 1)]
theorem atom1028Coded_decode : atom1028 = SparsePolynomial.decodeCubic 18 atom1028Coded := by decide +kernel
theorem atom1028Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3736455360 : Int) atom1028Coded) := by
  have h := atom1028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1029 : SparsePolynomial.Poly := [([9,16,17], 1)]
theorem eval_atom1029 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14476765080 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029Coded : CoefficientMerge.Poly := [(3221, 1)]
theorem atom1029Coded_decode : atom1029 = SparsePolynomial.decodeCubic 18 atom1029Coded := by decide +kernel
theorem atom1029Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14476765080 : Int) atom1029Coded) := by
  have h := atom1029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1030 : SparsePolynomial.Poly := [([9,17,17], 1)]
theorem eval_atom1030 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9901097400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030Coded : CoefficientMerge.Poly := [(3239, 1)]
theorem atom1030Coded_decode : atom1030 = SparsePolynomial.decodeCubic 18 atom1030Coded := by decide +kernel
theorem atom1030Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9901097400 : Int) atom1030Coded) := by
  have h := atom1030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1031 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom1031 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111329280 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031Coded : CoefficientMerge.Poly := [(3430, 1)]
theorem atom1031Coded_decode : atom1031 = SparsePolynomial.decodeCubic 18 atom1031Coded := by decide +kernel
theorem atom1031Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (111329280 : Int) atom1031Coded) := by
  have h := atom1031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1032 : SparsePolynomial.Poly := [([10,10,14], 1)]
theorem eval_atom1032 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 10) * (g 10) * (g 14)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (608461200 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032Coded : CoefficientMerge.Poly := [(3434, 1)]
theorem atom1032Coded_decode : atom1032 = SparsePolynomial.decodeCubic 18 atom1032Coded := by decide +kernel
theorem atom1032Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (608461200 : Int) atom1032Coded) := by
  have h := atom1032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1033 : SparsePolynomial.Poly := [([10,10,17], 1)]
theorem eval_atom1033 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 10) * (g 10) * (g 17)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290756160 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033Coded : CoefficientMerge.Poly := [(3437, 1)]
theorem atom1033Coded_decode : atom1033 = SparsePolynomial.decodeCubic 18 atom1033Coded := by decide +kernel
theorem atom1033Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (290756160 : Int) atom1033Coded) := by
  have h := atom1033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1034 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom1034 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361543680 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034Coded : CoefficientMerge.Poly := [(3449, 1)]
theorem atom1034Coded_decode : atom1034 = SparsePolynomial.decodeCubic 18 atom1034Coded := by decide +kernel
theorem atom1034Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (361543680 : Int) atom1034Coded) := by
  have h := atom1034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1035 : SparsePolynomial.Poly := [([10,11,13], 1)]
theorem eval_atom1035 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (563374080 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035Coded : CoefficientMerge.Poly := [(3451, 1)]
theorem atom1035Coded_decode : atom1035 = SparsePolynomial.decodeCubic 18 atom1035Coded := by decide +kernel
theorem atom1035Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (563374080 : Int) atom1035Coded) := by
  have h := atom1035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1036 : SparsePolynomial.Poly := [([10,11,14], 1)]
theorem eval_atom1036 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3488312160 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036Coded : CoefficientMerge.Poly := [(3452, 1)]
theorem atom1036Coded_decode : atom1036 = SparsePolynomial.decodeCubic 18 atom1036Coded := by decide +kernel
theorem atom1036Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3488312160 : Int) atom1036Coded) := by
  have h := atom1036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1037 : SparsePolynomial.Poly := [([10,11,15], 1)]
theorem eval_atom1037 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 10) * (g 11) * (g 15)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3183114240 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037Coded : CoefficientMerge.Poly := [(3453, 1)]
theorem atom1037Coded_decode : atom1037 = SparsePolynomial.decodeCubic 18 atom1037Coded := by decide +kernel
theorem atom1037Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3183114240 : Int) atom1037Coded) := by
  have h := atom1037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1038 : SparsePolynomial.Poly := [([10,11,16], 1)]
theorem eval_atom1038 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 10) * (g 11) * (g 16)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3172515840 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038Coded : CoefficientMerge.Poly := [(3454, 1)]
theorem atom1038Coded_decode : atom1038 = SparsePolynomial.decodeCubic 18 atom1038Coded := by decide +kernel
theorem atom1038Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3172515840 : Int) atom1038Coded) := by
  have h := atom1038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1039 : SparsePolynomial.Poly := [([10,11,17], 1)]
theorem eval_atom1039 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7005994560 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039Coded : CoefficientMerge.Poly := [(3455, 1)]
theorem atom1039Coded_decode : atom1039 = SparsePolynomial.decodeCubic 18 atom1039Coded := by decide +kernel
theorem atom1039Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7005994560 : Int) atom1039Coded) := by
  have h := atom1039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1040 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom1040 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (607054560 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040Coded : CoefficientMerge.Poly := [(3468, 1)]
theorem atom1040Coded_decode : atom1040 = SparsePolynomial.decodeCubic 18 atom1040Coded := by decide +kernel
theorem atom1040Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (607054560 : Int) atom1040Coded) := by
  have h := atom1040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1041 : SparsePolynomial.Poly := [([10,12,13], 1)]
theorem eval_atom1041 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2189573280 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041Coded : CoefficientMerge.Poly := [(3469, 1)]
theorem atom1041Coded_decode : atom1041 = SparsePolynomial.decodeCubic 18 atom1041Coded := by decide +kernel
theorem atom1041Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2189573280 : Int) atom1041Coded) := by
  have h := atom1041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1042 : SparsePolynomial.Poly := [([10,12,14], 1)]
theorem eval_atom1042 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8978554560 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042Coded : CoefficientMerge.Poly := [(3470, 1)]
theorem atom1042Coded_decode : atom1042 = SparsePolynomial.decodeCubic 18 atom1042Coded := by decide +kernel
theorem atom1042Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8978554560 : Int) atom1042Coded) := by
  have h := atom1042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1043 : SparsePolynomial.Poly := [([10,12,15], 1)]
theorem eval_atom1043 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 10) * (g 12) * (g 15)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9933636240 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043Coded : CoefficientMerge.Poly := [(3471, 1)]
theorem atom1043Coded_decode : atom1043 = SparsePolynomial.decodeCubic 18 atom1043Coded := by decide +kernel
theorem atom1043Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9933636240 : Int) atom1043Coded) := by
  have h := atom1043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1044 : SparsePolynomial.Poly := [([10,12,16], 1)]
theorem eval_atom1044 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 10) * (g 12) * (g 16)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7760603040 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044Coded : CoefficientMerge.Poly := [(3472, 1)]
theorem atom1044Coded_decode : atom1044 = SparsePolynomial.decodeCubic 18 atom1044Coded := by decide +kernel
theorem atom1044Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7760603040 : Int) atom1044Coded) := by
  have h := atom1044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1045 : SparsePolynomial.Poly := [([10,12,17], 1)]
theorem eval_atom1045 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 10) * (g 12) * (g 17)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14735798280 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045Coded : CoefficientMerge.Poly := [(3473, 1)]
theorem atom1045Coded_decode : atom1045 = SparsePolynomial.decodeCubic 18 atom1045Coded := by decide +kernel
theorem atom1045Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14735798280 : Int) atom1045Coded) := by
  have h := atom1045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1046 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom1046 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (822409728 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046Coded : CoefficientMerge.Poly := [(3487, 1)]
theorem atom1046Coded_decode : atom1046 = SparsePolynomial.decodeCubic 18 atom1046Coded := by decide +kernel
theorem atom1046Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (822409728 : Int) atom1046Coded) := by
  have h := atom1046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1047 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom1047 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7688157720 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047Coded : CoefficientMerge.Poly := [(3488, 1)]
theorem atom1047Coded_decode : atom1047 = SparsePolynomial.decodeCubic 18 atom1047Coded := by decide +kernel
theorem atom1047Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7688157720 : Int) atom1047Coded) := by
  have h := atom1047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1048 : SparsePolynomial.Poly := [([10,13,15], 1)]
theorem eval_atom1048 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 10) * (g 13) * (g 15)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10652866320 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048Coded : CoefficientMerge.Poly := [(3489, 1)]
theorem atom1048Coded_decode : atom1048 = SparsePolynomial.decodeCubic 18 atom1048Coded := by decide +kernel
theorem atom1048Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10652866320 : Int) atom1048Coded) := by
  have h := atom1048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1049 : SparsePolynomial.Poly := [([10,13,16], 1)]
theorem eval_atom1049 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 10) * (g 13) * (g 16)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9786183360 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049Coded : CoefficientMerge.Poly := [(3490, 1)]
theorem atom1049Coded_decode : atom1049 = SparsePolynomial.decodeCubic 18 atom1049Coded := by decide +kernel
theorem atom1049Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9786183360 : Int) atom1049Coded) := by
  have h := atom1049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1050 : SparsePolynomial.Poly := [([10,13,17], 1)]
theorem eval_atom1050 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 10) * (g 13) * (g 17)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14531488920 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050Coded : CoefficientMerge.Poly := [(3491, 1)]
theorem atom1050Coded_decode : atom1050 = SparsePolynomial.decodeCubic 18 atom1050Coded := by decide +kernel
theorem atom1050Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14531488920 : Int) atom1050Coded) := by
  have h := atom1050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1051 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom1051 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7183548600 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051Coded : CoefficientMerge.Poly := [(3506, 1)]
theorem atom1051Coded_decode : atom1051 = SparsePolynomial.decodeCubic 18 atom1051Coded := by decide +kernel
theorem atom1051Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7183548600 : Int) atom1051Coded) := by
  have h := atom1051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1052 : SparsePolynomial.Poly := [([10,14,15], 1)]
theorem eval_atom1052 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 10) * (g 14) * (g 15)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14604209880 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052Coded : CoefficientMerge.Poly := [(3507, 1)]
theorem atom1052Coded_decode : atom1052 = SparsePolynomial.decodeCubic 18 atom1052Coded := by decide +kernel
theorem atom1052Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14604209880 : Int) atom1052Coded) := by
  have h := atom1052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1053 : SparsePolynomial.Poly := [([10,14,16], 1)]
theorem eval_atom1053 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 10) * (g 14) * (g 16)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13859975280 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053Coded : CoefficientMerge.Poly := [(3508, 1)]
theorem atom1053Coded_decode : atom1053 = SparsePolynomial.decodeCubic 18 atom1053Coded := by decide +kernel
theorem atom1053Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13859975280 : Int) atom1053Coded) := by
  have h := atom1053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1054 : SparsePolynomial.Poly := [([10,14,17], 1)]
theorem eval_atom1054 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 10) * (g 14) * (g 17)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19964871120 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054Coded : CoefficientMerge.Poly := [(3509, 1)]
theorem atom1054Coded_decode : atom1054 = SparsePolynomial.decodeCubic 18 atom1054Coded := by decide +kernel
theorem atom1054Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (19964871120 : Int) atom1054Coded) := by
  have h := atom1054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block013 : CoefficientMerge.Poly := [(2820, 1914984960), (2821, 4619473920), (2822, 10744620960), (2823, 11856384000), (2824, 9369254400), (2825, 15816660480), (2839, 1790734848), (2840, 8615461560), (2841, 10629073920), (2842, 8825487360), (2843, 12648821760), (2858, 7466756280), (2859, 13350688440), (2860, 11285680080), (2861, 16222276560), (2877, 4506685440), (2878, 8103102720), (2879, 13606763520), (2896, 2134348800), (2897, 10271395200), (2915, 7369979520), (3087, 116904960), (3092, 16292880), (3106, 115061760), (3109, 285358080), (3110, 1766186400), (3111, 1621401600), (3112, 2672087040), (3113, 4110834240), (3125, 684334080), (3127, 279352320), (3128, 3051218400), (3129, 3584509440), (3130, 4543349760), (3131, 9320682240), (3144, 1234574880), (3145, 3395495520), (3146, 9850293120), (3147, 10984189680), (3148, 8721034080), (3149, 15410525400), (3163, 1293992448), (3164, 8110518360), (3165, 10591613040), (3166, 9273572160), (3167, 13553859240), (3182, 7312572600), (3183, 13858747800), (3184, 12444452400), (3185, 18040793520), (3201, 5224906320), (3202, 10468372560), (3203, 16825456200), (3220, 3736455360), (3221, 14476765080), (3239, 9901097400), (3430, 111329280), (3434, 608461200), (3437, 290756160), (3449, 361543680), (3451, 563374080), (3452, 3488312160), (3453, 3183114240), (3454, 3172515840), (3455, 7005994560), (3468, 607054560), (3469, 2189573280), (3470, 8978554560), (3471, 9933636240), (3472, 7760603040), (3473, 14735798280), (3487, 822409728), (3488, 7688157720), (3489, 10652866320), (3490, 9786183360), (3491, 14531488920), (3506, 7183548600), (3507, 14604209880), (3508, 13859975280), (3509, 19964871120)]
theorem block013_data : block013 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1914984960 : Int) atom0975Coded) (CoefficientMerge.scale (4619473920 : Int) atom0976Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10744620960 : Int) atom0977Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11856384000 : Int) atom0978Coded) (CoefficientMerge.scale (9369254400 : Int) atom0979Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15816660480 : Int) atom0980Coded) (CoefficientMerge.scale (1790734848 : Int) atom0981Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8615461560 : Int) atom0982Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10629073920 : Int) atom0983Coded) (CoefficientMerge.scale (8825487360 : Int) atom0984Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12648821760 : Int) atom0985Coded) (CoefficientMerge.scale (7466756280 : Int) atom0986Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13350688440 : Int) atom0987Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11285680080 : Int) atom0988Coded) (CoefficientMerge.scale (16222276560 : Int) atom0989Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4506685440 : Int) atom0990Coded) (CoefficientMerge.scale (8103102720 : Int) atom0991Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13606763520 : Int) atom0992Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2134348800 : Int) atom0993Coded) (CoefficientMerge.scale (10271395200 : Int) atom0994Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7369979520 : Int) atom0995Coded) (CoefficientMerge.scale (116904960 : Int) atom0996Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16292880 : Int) atom0997Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115061760 : Int) atom0998Coded) (CoefficientMerge.scale (285358080 : Int) atom0999Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1766186400 : Int) atom1000Coded) (CoefficientMerge.scale (1621401600 : Int) atom1001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672087040 : Int) atom1002Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4110834240 : Int) atom1003Coded) (CoefficientMerge.scale (684334080 : Int) atom1004Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (279352320 : Int) atom1005Coded) (CoefficientMerge.scale (3051218400 : Int) atom1006Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3584509440 : Int) atom1007Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4543349760 : Int) atom1008Coded) (CoefficientMerge.scale (9320682240 : Int) atom1009Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1234574880 : Int) atom1010Coded) (CoefficientMerge.scale (3395495520 : Int) atom1011Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9850293120 : Int) atom1012Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10984189680 : Int) atom1013Coded) (CoefficientMerge.scale (8721034080 : Int) atom1014Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15410525400 : Int) atom1015Coded) (CoefficientMerge.scale (1293992448 : Int) atom1016Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8110518360 : Int) atom1017Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10591613040 : Int) atom1018Coded) (CoefficientMerge.scale (9273572160 : Int) atom1019Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13553859240 : Int) atom1020Coded) (CoefficientMerge.scale (7312572600 : Int) atom1021Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13858747800 : Int) atom1022Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12444452400 : Int) atom1023Coded) (CoefficientMerge.scale (18040793520 : Int) atom1024Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5224906320 : Int) atom1025Coded) (CoefficientMerge.scale (10468372560 : Int) atom1026Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16825456200 : Int) atom1027Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3736455360 : Int) atom1028Coded) (CoefficientMerge.scale (14476765080 : Int) atom1029Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9901097400 : Int) atom1030Coded) (CoefficientMerge.scale (111329280 : Int) atom1031Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (608461200 : Int) atom1032Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (290756160 : Int) atom1033Coded) (CoefficientMerge.scale (361543680 : Int) atom1034Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (563374080 : Int) atom1035Coded) (CoefficientMerge.scale (3488312160 : Int) atom1036Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3183114240 : Int) atom1037Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3172515840 : Int) atom1038Coded) (CoefficientMerge.scale (7005994560 : Int) atom1039Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (607054560 : Int) atom1040Coded) (CoefficientMerge.scale (2189573280 : Int) atom1041Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8978554560 : Int) atom1042Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9933636240 : Int) atom1043Coded) (CoefficientMerge.scale (7760603040 : Int) atom1044Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14735798280 : Int) atom1045Coded) (CoefficientMerge.scale (822409728 : Int) atom1046Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7688157720 : Int) atom1047Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10652866320 : Int) atom1048Coded) (CoefficientMerge.scale (9786183360 : Int) atom1049Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14531488920 : Int) atom1050Coded) (CoefficientMerge.scale (7183548600 : Int) atom1051Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14604209880 : Int) atom1052Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13859975280 : Int) atom1053Coded) (CoefficientMerge.scale (19964871120 : Int) atom1054Coded)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block013 := by
  rw [block013_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0975Coded_nonneg g hg hA hB) (atom0976Coded_nonneg g hg hA hB)) (add_nonneg (atom0977Coded_nonneg g hg hA hB) (add_nonneg (atom0978Coded_nonneg g hg hA hB) (atom0979Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0980Coded_nonneg g hg hA hB) (atom0981Coded_nonneg g hg hA hB)) (add_nonneg (atom0982Coded_nonneg g hg hA hB) (add_nonneg (atom0983Coded_nonneg g hg hA hB) (atom0984Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0985Coded_nonneg g hg hA hB) (atom0986Coded_nonneg g hg hA hB)) (add_nonneg (atom0987Coded_nonneg g hg hA hB) (add_nonneg (atom0988Coded_nonneg g hg hA hB) (atom0989Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0990Coded_nonneg g hg hA hB) (atom0991Coded_nonneg g hg hA hB)) (add_nonneg (atom0992Coded_nonneg g hg hA hB) (add_nonneg (atom0993Coded_nonneg g hg hA hB) (atom0994Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0995Coded_nonneg g hg hA hB) (atom0996Coded_nonneg g hg hA hB)) (add_nonneg (atom0997Coded_nonneg g hg hA hB) (add_nonneg (atom0998Coded_nonneg g hg hA hB) (atom0999Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1000Coded_nonneg g hg hA hB) (atom1001Coded_nonneg g hg hA hB)) (add_nonneg (atom1002Coded_nonneg g hg hA hB) (add_nonneg (atom1003Coded_nonneg g hg hA hB) (atom1004Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1005Coded_nonneg g hg hA hB) (atom1006Coded_nonneg g hg hA hB)) (add_nonneg (atom1007Coded_nonneg g hg hA hB) (add_nonneg (atom1008Coded_nonneg g hg hA hB) (atom1009Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1010Coded_nonneg g hg hA hB) (atom1011Coded_nonneg g hg hA hB)) (add_nonneg (atom1012Coded_nonneg g hg hA hB) (add_nonneg (atom1013Coded_nonneg g hg hA hB) (atom1014Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1015Coded_nonneg g hg hA hB) (atom1016Coded_nonneg g hg hA hB)) (add_nonneg (atom1017Coded_nonneg g hg hA hB) (add_nonneg (atom1018Coded_nonneg g hg hA hB) (atom1019Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1020Coded_nonneg g hg hA hB) (atom1021Coded_nonneg g hg hA hB)) (add_nonneg (atom1022Coded_nonneg g hg hA hB) (add_nonneg (atom1023Coded_nonneg g hg hA hB) (atom1024Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1025Coded_nonneg g hg hA hB) (atom1026Coded_nonneg g hg hA hB)) (add_nonneg (atom1027Coded_nonneg g hg hA hB) (add_nonneg (atom1028Coded_nonneg g hg hA hB) (atom1029Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1030Coded_nonneg g hg hA hB) (atom1031Coded_nonneg g hg hA hB)) (add_nonneg (atom1032Coded_nonneg g hg hA hB) (add_nonneg (atom1033Coded_nonneg g hg hA hB) (atom1034Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1035Coded_nonneg g hg hA hB) (atom1036Coded_nonneg g hg hA hB)) (add_nonneg (atom1037Coded_nonneg g hg hA hB) (add_nonneg (atom1038Coded_nonneg g hg hA hB) (atom1039Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1040Coded_nonneg g hg hA hB) (atom1041Coded_nonneg g hg hA hB)) (add_nonneg (atom1042Coded_nonneg g hg hA hB) (add_nonneg (atom1043Coded_nonneg g hg hA hB) (atom1044Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1045Coded_nonneg g hg hA hB) (atom1046Coded_nonneg g hg hA hB)) (add_nonneg (atom1047Coded_nonneg g hg hA hB) (add_nonneg (atom1048Coded_nonneg g hg hA hB) (atom1049Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1050Coded_nonneg g hg hA hB) (atom1051Coded_nonneg g hg hA hB)) (add_nonneg (atom1052Coded_nonneg g hg hA hB) (add_nonneg (atom1053Coded_nonneg g hg hA hB) (atom1054Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
