import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom1135 : SparsePolynomial.Poly := [([15,17,17], 1)]
theorem eval_atom1135 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1135 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1135_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4737761280 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135Coded : CoefficientMerge.Poly := [(5183, 1)]
theorem atom1135Coded_decode : atom1135 = SparsePolynomial.decodeCubic 18 atom1135Coded := by decide +kernel
theorem atom1135Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) := by
  have h := atom1135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1136 : SparsePolynomial.Poly := [([16,16,16], 1)]
theorem eval_atom1136 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1136 = ((g 16) * (g 16) * (g 16)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1136_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3915233280 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 16) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1136Coded : CoefficientMerge.Poly := [(5488, 1)]
theorem atom1136Coded_decode : atom1136 = SparsePolynomial.decodeCubic 18 atom1136Coded := by decide +kernel
theorem atom1136Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded) := by
  have h := atom1136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1137 : SparsePolynomial.Poly := [([16,16,17], 1)]
theorem eval_atom1137 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1137 = ((g 16) * (g 16) * (g 17)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1137_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9716797440 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137Coded : CoefficientMerge.Poly := [(5489, 1)]
theorem atom1137Coded_decode : atom1137 = SparsePolynomial.decodeCubic 18 atom1137Coded := by decide +kernel
theorem atom1137Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) := by
  have h := atom1137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1138 : SparsePolynomial.Poly := [([16,17,17], 1)]
theorem eval_atom1138 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1138 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1138_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5922201600 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138Coded : CoefficientMerge.Poly := [(5507, 1)]
theorem atom1138Coded_decode : atom1138 = SparsePolynomial.decodeCubic 18 atom1138Coded := by decide +kernel
theorem atom1138Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded) := by
  have h := atom1138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block015 : CoefficientMerge.Poly := [(5183, 4737761280), (5488, 3915233280), (5489, 9716797440), (5507, 5922201600)]
theorem block015_data : block015 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded))) := by decide +kernel
theorem block015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block015 := by
  rw [block015_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (atom1135Coded_nonneg g hg hA hB) (atom1136Coded_nonneg g hg hA hB)) (add_nonneg (atom1137Coded_nonneg g hg hA hB) (atom1138Coded_nonneg g hg hA hB)))

end APPT.Finite18
