import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1009 : SparsePolynomial.Poly := [([2,17,23], 1)]
theorem eval_atom1009 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1009 = ((g 2) * (g 17) * (g 23)) := by
  norm_num [atom1009, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475798210272000 : Int) atom1009) := by
  rw [SparsePolynomial.eval_scale, eval_atom1009]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1009Coded : CoefficientMerge.Poly := [(1583, 1)]
theorem atom1009Coded_decode : atom1009 = SparsePolynomial.decodeCubic 24 atom1009Coded := by decide +kernel
theorem atom1009Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (475798210272000 : Int) atom1009Coded) := by
  have h := atom1009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1010 : SparsePolynomial.Poly := [([2,18,18], 1)]
theorem eval_atom1010 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1010 = ((g 2) * (g 18) * (g 18)) := by
  norm_num [atom1010, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290294848166400 : Int) atom1010) := by
  rw [SparsePolynomial.eval_scale, eval_atom1010]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1010Coded : CoefficientMerge.Poly := [(1602, 1)]
theorem atom1010Coded_decode : atom1010 = SparsePolynomial.decodeCubic 24 atom1010Coded := by decide +kernel
theorem atom1010Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (290294848166400 : Int) atom1010Coded) := by
  have h := atom1010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1011 : SparsePolynomial.Poly := [([2,18,19], 1)]
theorem eval_atom1011 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1011 = ((g 2) * (g 18) * (g 19)) := by
  norm_num [atom1011, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (476361662515200 : Int) atom1011) := by
  rw [SparsePolynomial.eval_scale, eval_atom1011]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1011Coded : CoefficientMerge.Poly := [(1603, 1)]
theorem atom1011Coded_decode : atom1011 = SparsePolynomial.decodeCubic 24 atom1011Coded := by decide +kernel
theorem atom1011Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (476361662515200 : Int) atom1011Coded) := by
  have h := atom1011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1012 : SparsePolynomial.Poly := [([2,18,20], 1)]
theorem eval_atom1012 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1012 = ((g 2) * (g 18) * (g 20)) := by
  norm_num [atom1012, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (653817225600000 : Int) atom1012) := by
  rw [SparsePolynomial.eval_scale, eval_atom1012]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1012Coded : CoefficientMerge.Poly := [(1604, 1)]
theorem atom1012Coded_decode : atom1012 = SparsePolynomial.decodeCubic 24 atom1012Coded := by decide +kernel
theorem atom1012Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (653817225600000 : Int) atom1012Coded) := by
  have h := atom1012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1013 : SparsePolynomial.Poly := [([2,18,21], 1)]
theorem eval_atom1013 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1013 = ((g 2) * (g 18) * (g 21)) := by
  norm_num [atom1013, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (549589191782400 : Int) atom1013) := by
  rw [SparsePolynomial.eval_scale, eval_atom1013]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1013Coded : CoefficientMerge.Poly := [(1605, 1)]
theorem atom1013Coded_decode : atom1013 = SparsePolynomial.decodeCubic 24 atom1013Coded := by decide +kernel
theorem atom1013Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (549589191782400 : Int) atom1013Coded) := by
  have h := atom1013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1014 : SparsePolynomial.Poly := [([2,18,22], 1)]
theorem eval_atom1014 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1014 = ((g 2) * (g 18) * (g 22)) := by
  norm_num [atom1014, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349197353164800 : Int) atom1014) := by
  rw [SparsePolynomial.eval_scale, eval_atom1014]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1014Coded : CoefficientMerge.Poly := [(1606, 1)]
theorem atom1014Coded_decode : atom1014 = SparsePolynomial.decodeCubic 24 atom1014Coded := by decide +kernel
theorem atom1014Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349197353164800 : Int) atom1014Coded) := by
  have h := atom1014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1015 : SparsePolynomial.Poly := [([2,18,23], 1)]
theorem eval_atom1015 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1015 = ((g 2) * (g 18) * (g 23)) := by
  norm_num [atom1015, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (503137604138400 : Int) atom1015) := by
  rw [SparsePolynomial.eval_scale, eval_atom1015]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1015Coded : CoefficientMerge.Poly := [(1607, 1)]
theorem atom1015Coded_decode : atom1015 = SparsePolynomial.decodeCubic 24 atom1015Coded := by decide +kernel
theorem atom1015Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (503137604138400 : Int) atom1015Coded) := by
  have h := atom1015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1016 : SparsePolynomial.Poly := [([2,19,19], 1)]
theorem eval_atom1016 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1016 = ((g 2) * (g 19) * (g 19)) := by
  norm_num [atom1016, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186615382947840 : Int) atom1016) := by
  rw [SparsePolynomial.eval_scale, eval_atom1016]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1016Coded : CoefficientMerge.Poly := [(1627, 1)]
theorem atom1016Coded_decode : atom1016 = SparsePolynomial.decodeCubic 24 atom1016Coded := by decide +kernel
theorem atom1016Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186615382947840 : Int) atom1016Coded) := by
  have h := atom1016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1017 : SparsePolynomial.Poly := [([2,19,20], 1)]
theorem eval_atom1017 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1017 = ((g 2) * (g 19) * (g 20)) := by
  norm_num [atom1017, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (534152726553600 : Int) atom1017) := by
  rw [SparsePolynomial.eval_scale, eval_atom1017]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1017Coded : CoefficientMerge.Poly := [(1628, 1)]
theorem atom1017Coded_decode : atom1017 = SparsePolynomial.decodeCubic 24 atom1017Coded := by decide +kernel
theorem atom1017Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (534152726553600 : Int) atom1017Coded) := by
  have h := atom1017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1018 : SparsePolynomial.Poly := [([2,19,21], 1)]
theorem eval_atom1018 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1018 = ((g 2) * (g 19) * (g 21)) := by
  norm_num [atom1018, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (503407370188800 : Int) atom1018) := by
  rw [SparsePolynomial.eval_scale, eval_atom1018]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1018Coded : CoefficientMerge.Poly := [(1629, 1)]
theorem atom1018Coded_decode : atom1018 = SparsePolynomial.decodeCubic 24 atom1018Coded := by decide +kernel
theorem atom1018Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (503407370188800 : Int) atom1018Coded) := by
  have h := atom1018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1019 : SparsePolynomial.Poly := [([2,19,22], 1)]
theorem eval_atom1019 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1019 = ((g 2) * (g 19) * (g 22)) := by
  norm_num [atom1019, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347292762163200 : Int) atom1019) := by
  rw [SparsePolynomial.eval_scale, eval_atom1019]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1019Coded : CoefficientMerge.Poly := [(1630, 1)]
theorem atom1019Coded_decode : atom1019 = SparsePolynomial.decodeCubic 24 atom1019Coded := by decide +kernel
theorem atom1019Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347292762163200 : Int) atom1019Coded) := by
  have h := atom1019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1020 : SparsePolynomial.Poly := [([2,19,23], 1)]
theorem eval_atom1020 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1020 = ((g 2) * (g 19) * (g 23)) := by
  norm_num [atom1020, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386611959333600 : Int) atom1020) := by
  rw [SparsePolynomial.eval_scale, eval_atom1020]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1020Coded : CoefficientMerge.Poly := [(1631, 1)]
theorem atom1020Coded_decode : atom1020 = SparsePolynomial.decodeCubic 24 atom1020Coded := by decide +kernel
theorem atom1020Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (386611959333600 : Int) atom1020Coded) := by
  have h := atom1020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1021 : SparsePolynomial.Poly := [([2,20,20], 1)]
theorem eval_atom1021 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1021 = ((g 2) * (g 20) * (g 20)) := by
  norm_num [atom1021, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (348085912204800 : Int) atom1021) := by
  rw [SparsePolynomial.eval_scale, eval_atom1021]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1021Coded : CoefficientMerge.Poly := [(1652, 1)]
theorem atom1021Coded_decode : atom1021 = SparsePolynomial.decodeCubic 24 atom1021Coded := by decide +kernel
theorem atom1021Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (348085912204800 : Int) atom1021Coded) := by
  have h := atom1021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1022 : SparsePolynomial.Poly := [([2,20,21], 1)]
theorem eval_atom1022 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1022 = ((g 2) * (g 20) * (g 21)) := by
  norm_num [atom1022, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (527646447820800 : Int) atom1022) := by
  rw [SparsePolynomial.eval_scale, eval_atom1022]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1022Coded : CoefficientMerge.Poly := [(1653, 1)]
theorem atom1022Coded_decode : atom1022 = SparsePolynomial.decodeCubic 24 atom1022Coded := by decide +kernel
theorem atom1022Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (527646447820800 : Int) atom1022Coded) := by
  have h := atom1022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1023 : SparsePolynomial.Poly := [([2,20,22], 1)]
theorem eval_atom1023 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1023 = ((g 2) * (g 20) * (g 22)) := by
  norm_num [atom1023, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345267040204800 : Int) atom1023) := by
  rw [SparsePolynomial.eval_scale, eval_atom1023]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1023Coded : CoefficientMerge.Poly := [(1654, 1)]
theorem atom1023Coded_decode : atom1023 = SparsePolynomial.decodeCubic 24 atom1023Coded := by decide +kernel
theorem atom1023Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345267040204800 : Int) atom1023Coded) := by
  have h := atom1023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1024 : SparsePolynomial.Poly := [([2,20,23], 1)]
theorem eval_atom1024 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1024 = ((g 2) * (g 20) * (g 23)) := by
  norm_num [atom1024, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404881632540000 : Int) atom1024) := by
  rw [SparsePolynomial.eval_scale, eval_atom1024]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1024Coded : CoefficientMerge.Poly := [(1655, 1)]
theorem atom1024Coded_decode : atom1024 = SparsePolynomial.decodeCubic 24 atom1024Coded := by decide +kernel
theorem atom1024Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (404881632540000 : Int) atom1024Coded) := by
  have h := atom1024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1025 : SparsePolynomial.Poly := [([2,21,21], 1)]
theorem eval_atom1025 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1025 = ((g 2) * (g 21) * (g 21)) := by
  norm_num [atom1025, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170311413888000 : Int) atom1025) := by
  rw [SparsePolynomial.eval_scale, eval_atom1025]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1025Coded : CoefficientMerge.Poly := [(1677, 1)]
theorem atom1025Coded_decode : atom1025 = SparsePolynomial.decodeCubic 24 atom1025Coded := by decide +kernel
theorem atom1025Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (170311413888000 : Int) atom1025Coded) := by
  have h := atom1025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1026 : SparsePolynomial.Poly := [([2,21,22], 1)]
theorem eval_atom1026 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1026 = ((g 2) * (g 21) * (g 22)) := by
  norm_num [atom1026, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217123374182400 : Int) atom1026) := by
  rw [SparsePolynomial.eval_scale, eval_atom1026]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1026Coded : CoefficientMerge.Poly := [(1678, 1)]
theorem atom1026Coded_decode : atom1026 = SparsePolynomial.decodeCubic 24 atom1026Coded := by decide +kernel
theorem atom1026Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217123374182400 : Int) atom1026Coded) := by
  have h := atom1026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1027 : SparsePolynomial.Poly := [([2,21,23], 1)]
theorem eval_atom1027 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1027 = ((g 2) * (g 21) * (g 23)) := by
  norm_num [atom1027, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (288355987735200 : Int) atom1027) := by
  rw [SparsePolynomial.eval_scale, eval_atom1027]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1027Coded : CoefficientMerge.Poly := [(1679, 1)]
theorem atom1027Coded_decode : atom1027 = SparsePolynomial.decodeCubic 24 atom1027Coded := by decide +kernel
theorem atom1027Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (288355987735200 : Int) atom1027Coded) := by
  have h := atom1027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1028 : SparsePolynomial.Poly := [([2,22,22], 1)]
theorem eval_atom1028 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1028 = ((g 2) * (g 22) * (g 22)) := by
  norm_num [atom1028, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8846586806400 : Int) atom1028) := by
  rw [SparsePolynomial.eval_scale, eval_atom1028]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1028Coded : CoefficientMerge.Poly := [(1702, 1)]
theorem atom1028Coded_decode : atom1028 = SparsePolynomial.decodeCubic 24 atom1028Coded := by decide +kernel
theorem atom1028Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8846586806400 : Int) atom1028Coded) := by
  have h := atom1028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1029 : SparsePolynomial.Poly := [([2,22,23], 1)]
theorem eval_atom1029 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1029 = ((g 2) * (g 22) * (g 23)) := by
  norm_num [atom1029, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100071607053600 : Int) atom1029) := by
  rw [SparsePolynomial.eval_scale, eval_atom1029]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1029Coded : CoefficientMerge.Poly := [(1703, 1)]
theorem atom1029Coded_decode : atom1029 = SparsePolynomial.decodeCubic 24 atom1029Coded := by decide +kernel
theorem atom1029Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100071607053600 : Int) atom1029Coded) := by
  have h := atom1029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1030 : SparsePolynomial.Poly := [([2,23,23], 1)]
theorem eval_atom1030 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1030 = ((g 2) * (g 23) * (g 23)) := by
  norm_num [atom1030, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78422186858400 : Int) atom1030) := by
  rw [SparsePolynomial.eval_scale, eval_atom1030]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1030Coded : CoefficientMerge.Poly := [(1727, 1)]
theorem atom1030Coded_decode : atom1030 = SparsePolynomial.decodeCubic 24 atom1030Coded := by decide +kernel
theorem atom1030Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78422186858400 : Int) atom1030Coded) := by
  have h := atom1030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1031 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom1031 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1031 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom1031, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23813830656000 : Int) atom1031) := by
  rw [SparsePolynomial.eval_scale, eval_atom1031]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1031Coded : CoefficientMerge.Poly := [(1803, 1)]
theorem atom1031Coded_decode : atom1031 = SparsePolynomial.decodeCubic 24 atom1031Coded := by decide +kernel
theorem atom1031Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (23813830656000 : Int) atom1031Coded) := by
  have h := atom1031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1032 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom1032 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1032 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom1032, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65232886118400 : Int) atom1032) := by
  rw [SparsePolynomial.eval_scale, eval_atom1032]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1032Coded : CoefficientMerge.Poly := [(1804, 1)]
theorem atom1032Coded_decode : atom1032 = SparsePolynomial.decodeCubic 24 atom1032Coded := by decide +kernel
theorem atom1032Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65232886118400 : Int) atom1032Coded) := by
  have h := atom1032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1033 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom1033 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1033 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom1033, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65907174009600 : Int) atom1033) := by
  rw [SparsePolynomial.eval_scale, eval_atom1033]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1033Coded : CoefficientMerge.Poly := [(1805, 1)]
theorem atom1033Coded_decode : atom1033 = SparsePolynomial.decodeCubic 24 atom1033Coded := by decide +kernel
theorem atom1033Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65907174009600 : Int) atom1033Coded) := by
  have h := atom1033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1034 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom1034 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1034 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom1034, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52815674419200 : Int) atom1034) := by
  rw [SparsePolynomial.eval_scale, eval_atom1034]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1034Coded : CoefficientMerge.Poly := [(1806, 1)]
theorem atom1034Coded_decode : atom1034 = SparsePolynomial.decodeCubic 24 atom1034Coded := by decide +kernel
theorem atom1034Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (52815674419200 : Int) atom1034Coded) := by
  have h := atom1034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1035 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom1035 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1035 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom1035, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1035_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46607068569600 : Int) atom1035) := by
  rw [SparsePolynomial.eval_scale, eval_atom1035]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1035Coded : CoefficientMerge.Poly := [(1807, 1)]
theorem atom1035Coded_decode : atom1035 = SparsePolynomial.decodeCubic 24 atom1035Coded := by decide +kernel
theorem atom1035Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46607068569600 : Int) atom1035Coded) := by
  have h := atom1035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1036 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom1036 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1036 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom1036, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1036_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40398462720000 : Int) atom1036) := by
  rw [SparsePolynomial.eval_scale, eval_atom1036]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1036Coded : CoefficientMerge.Poly := [(1808, 1)]
theorem atom1036Coded_decode : atom1036 = SparsePolynomial.decodeCubic 24 atom1036Coded := by decide +kernel
theorem atom1036Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40398462720000 : Int) atom1036Coded) := by
  have h := atom1036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1037 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom1037 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1037 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom1037, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1037_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40201637916528 : Int) atom1037) := by
  rw [SparsePolynomial.eval_scale, eval_atom1037]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1037Coded : CoefficientMerge.Poly := [(1809, 1)]
theorem atom1037Coded_decode : atom1037 = SparsePolynomial.decodeCubic 24 atom1037Coded := by decide +kernel
theorem atom1037Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40201637916528 : Int) atom1037Coded) := by
  have h := atom1037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1038 : SparsePolynomial.Poly := [([3,3,10], 1)]
theorem eval_atom1038 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1038 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom1038, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1038_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51636529101168 : Int) atom1038) := by
  rw [SparsePolynomial.eval_scale, eval_atom1038]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1038Coded : CoefficientMerge.Poly := [(1810, 1)]
theorem atom1038Coded_decode : atom1038 = SparsePolynomial.decodeCubic 24 atom1038Coded := by decide +kernel
theorem atom1038Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (51636529101168 : Int) atom1038Coded) := by
  have h := atom1038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1039 : SparsePolynomial.Poly := [([3,3,11], 1)]
theorem eval_atom1039 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1039 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom1039, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1039_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61432993046304 : Int) atom1039) := by
  rw [SparsePolynomial.eval_scale, eval_atom1039]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1039Coded : CoefficientMerge.Poly := [(1811, 1)]
theorem atom1039Coded_decode : atom1039 = SparsePolynomial.decodeCubic 24 atom1039Coded := by decide +kernel
theorem atom1039Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (61432993046304 : Int) atom1039Coded) := by
  have h := atom1039_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1039Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1040 : SparsePolynomial.Poly := [([3,3,12], 1)]
theorem eval_atom1040 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1040 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom1040, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1040_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83146369420224 : Int) atom1040) := by
  rw [SparsePolynomial.eval_scale, eval_atom1040]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1040Coded : CoefficientMerge.Poly := [(1812, 1)]
theorem atom1040Coded_decode : atom1040 = SparsePolynomial.decodeCubic 24 atom1040Coded := by decide +kernel
theorem atom1040Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83146369420224 : Int) atom1040Coded) := by
  have h := atom1040_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1040Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1041 : SparsePolynomial.Poly := [([3,3,13], 1)]
theorem eval_atom1041 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1041 = ((g 3) * (g 3) * (g 13)) := by
  norm_num [atom1041, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1041_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68276633040000 : Int) atom1041) := by
  rw [SparsePolynomial.eval_scale, eval_atom1041]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1041Coded : CoefficientMerge.Poly := [(1813, 1)]
theorem atom1041Coded_decode : atom1041 = SparsePolynomial.decodeCubic 24 atom1041Coded := by decide +kernel
theorem atom1041Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68276633040000 : Int) atom1041Coded) := by
  have h := atom1041_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1041Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1042 : SparsePolynomial.Poly := [([3,3,14], 1)]
theorem eval_atom1042 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1042 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom1042, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1042_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49732633843200 : Int) atom1042) := by
  rw [SparsePolynomial.eval_scale, eval_atom1042]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1042Coded : CoefficientMerge.Poly := [(1814, 1)]
theorem atom1042Coded_decode : atom1042 = SparsePolynomial.decodeCubic 24 atom1042Coded := by decide +kernel
theorem atom1042Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49732633843200 : Int) atom1042Coded) := by
  have h := atom1042_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1042Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1043 : SparsePolynomial.Poly := [([3,3,15], 1)]
theorem eval_atom1043 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1043 = ((g 3) * (g 3) * (g 15)) := by
  norm_num [atom1043, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1043_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45975641241600 : Int) atom1043) := by
  rw [SparsePolynomial.eval_scale, eval_atom1043]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1043Coded : CoefficientMerge.Poly := [(1815, 1)]
theorem atom1043Coded_decode : atom1043 = SparsePolynomial.decodeCubic 24 atom1043Coded := by decide +kernel
theorem atom1043Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45975641241600 : Int) atom1043Coded) := by
  have h := atom1043_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1043Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1044 : SparsePolynomial.Poly := [([3,3,16], 1)]
theorem eval_atom1044 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1044 = ((g 3) * (g 3) * (g 16)) := by
  norm_num [atom1044, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1044_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30396138393600 : Int) atom1044) := by
  rw [SparsePolynomial.eval_scale, eval_atom1044]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1044Coded : CoefficientMerge.Poly := [(1816, 1)]
theorem atom1044Coded_decode : atom1044 = SparsePolynomial.decodeCubic 24 atom1044Coded := by decide +kernel
theorem atom1044Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30396138393600 : Int) atom1044Coded) := by
  have h := atom1044_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1044Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1045 : SparsePolynomial.Poly := [([3,3,17], 1)]
theorem eval_atom1045 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1045 = ((g 3) * (g 3) * (g 17)) := by
  norm_num [atom1045, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1045_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24749374003200 : Int) atom1045) := by
  rw [SparsePolynomial.eval_scale, eval_atom1045]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1045Coded : CoefficientMerge.Poly := [(1817, 1)]
theorem atom1045Coded_decode : atom1045 = SparsePolynomial.decodeCubic 24 atom1045Coded := by decide +kernel
theorem atom1045Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24749374003200 : Int) atom1045Coded) := by
  have h := atom1045_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1045Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1046 : SparsePolynomial.Poly := [([3,3,18], 1)]
theorem eval_atom1046 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1046 = ((g 3) * (g 3) * (g 18)) := by
  norm_num [atom1046, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1046_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48733303449600 : Int) atom1046) := by
  rw [SparsePolynomial.eval_scale, eval_atom1046]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1046Coded : CoefficientMerge.Poly := [(1818, 1)]
theorem atom1046Coded_decode : atom1046 = SparsePolynomial.decodeCubic 24 atom1046Coded := by decide +kernel
theorem atom1046Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48733303449600 : Int) atom1046Coded) := by
  have h := atom1046_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1046Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1047 : SparsePolynomial.Poly := [([3,3,20], 1)]
theorem eval_atom1047 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1047 = ((g 3) * (g 3) * (g 20)) := by
  norm_num [atom1047, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1047_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36316091750400 : Int) atom1047) := by
  rw [SparsePolynomial.eval_scale, eval_atom1047]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1047Coded : CoefficientMerge.Poly := [(1820, 1)]
theorem atom1047Coded_decode : atom1047 = SparsePolynomial.decodeCubic 24 atom1047Coded := by decide +kernel
theorem atom1047Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36316091750400 : Int) atom1047Coded) := by
  have h := atom1047_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1047Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1048 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom1048 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1048 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom1048, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1048_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63987427929600 : Int) atom1048) := by
  rw [SparsePolynomial.eval_scale, eval_atom1048]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1048Coded : CoefficientMerge.Poly := [(1828, 1)]
theorem atom1048Coded_decode : atom1048 = SparsePolynomial.decodeCubic 24 atom1048Coded := by decide +kernel
theorem atom1048Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63987427929600 : Int) atom1048Coded) := by
  have h := atom1048_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1048Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1049 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom1049 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1049 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom1049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1049_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107581417564896 : Int) atom1049) := by
  rw [SparsePolynomial.eval_scale, eval_atom1049]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1049Coded : CoefficientMerge.Poly := [(1829, 1)]
theorem atom1049Coded_decode : atom1049 = SparsePolynomial.decodeCubic 24 atom1049Coded := by decide +kernel
theorem atom1049Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107581417564896 : Int) atom1049Coded) := by
  have h := atom1049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1050 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom1050 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1050 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom1050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1050_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76714554470400 : Int) atom1050) := by
  rw [SparsePolynomial.eval_scale, eval_atom1050]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1050Coded : CoefficientMerge.Poly := [(1830, 1)]
theorem atom1050Coded_decode : atom1050 = SparsePolynomial.decodeCubic 24 atom1050Coded := by decide +kernel
theorem atom1050Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (76714554470400 : Int) atom1050Coded) := by
  have h := atom1050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1051 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom1051 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1051 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom1051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1051_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68379713740800 : Int) atom1051) := by
  rw [SparsePolynomial.eval_scale, eval_atom1051]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1051Coded : CoefficientMerge.Poly := [(1831, 1)]
theorem atom1051Coded_decode : atom1051 = SparsePolynomial.decodeCubic 24 atom1051Coded := by decide +kernel
theorem atom1051Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68379713740800 : Int) atom1051Coded) := by
  have h := atom1051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1052 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom1052 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1052 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom1052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1052_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60044873011200 : Int) atom1052) := by
  rw [SparsePolynomial.eval_scale, eval_atom1052]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1052Coded : CoefficientMerge.Poly := [(1832, 1)]
theorem atom1052Coded_decode : atom1052 = SparsePolynomial.decodeCubic 24 atom1052Coded := by decide +kernel
theorem atom1052Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60044873011200 : Int) atom1052Coded) := by
  have h := atom1052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1053 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom1053 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1053 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom1053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1053_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63733594373856 : Int) atom1053) := by
  rw [SparsePolynomial.eval_scale, eval_atom1053]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1053Coded : CoefficientMerge.Poly := [(1833, 1)]
theorem atom1053Coded_decode : atom1053 = SparsePolynomial.decodeCubic 24 atom1053Coded := by decide +kernel
theorem atom1053Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63733594373856 : Int) atom1053Coded) := by
  have h := atom1053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1054 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom1054 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1054 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom1054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1054_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90685747712736 : Int) atom1054) := by
  rw [SparsePolynomial.eval_scale, eval_atom1054]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1054Coded : CoefficientMerge.Poly := [(1834, 1)]
theorem atom1054Coded_decode : atom1054 = SparsePolynomial.decodeCubic 24 atom1054Coded := by decide +kernel
theorem atom1054Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90685747712736 : Int) atom1054Coded) := by
  have h := atom1054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1055 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom1055 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1055 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1055_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114361046572608 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1055Coded : CoefficientMerge.Poly := [(1835, 1)]
theorem atom1055Coded_decode : atom1055 = SparsePolynomial.decodeCubic 24 atom1055Coded := by decide +kernel
theorem atom1055Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (114361046572608 : Int) atom1055Coded) := by
  have h := atom1055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1056 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom1056 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1056 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1056_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161870170290048 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1056Coded : CoefficientMerge.Poly := [(1836, 1)]
theorem atom1056Coded_decode : atom1056 = SparsePolynomial.decodeCubic 24 atom1056Coded := by decide +kernel
theorem atom1056Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161870170290048 : Int) atom1056Coded) := by
  have h := atom1056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1057 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom1057 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1057 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1057_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136213068499200 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057Coded : CoefficientMerge.Poly := [(1837, 1)]
theorem atom1057Coded_decode : atom1057 = SparsePolynomial.decodeCubic 24 atom1057Coded := by decide +kernel
theorem atom1057Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136213068499200 : Int) atom1057Coded) := by
  have h := atom1057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1058 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom1058 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1058 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1058_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103207441075200 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058Coded : CoefficientMerge.Poly := [(1838, 1)]
theorem atom1058Coded_decode : atom1058 = SparsePolynomial.decodeCubic 24 atom1058Coded := by decide +kernel
theorem atom1058Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103207441075200 : Int) atom1058Coded) := by
  have h := atom1058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1059 : SparsePolynomial.Poly := [([3,4,15], 1)]
theorem eval_atom1059 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1059 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1059_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99775826841600 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059Coded : CoefficientMerge.Poly := [(1839, 1)]
theorem atom1059Coded_decode : atom1059 = SparsePolynomial.decodeCubic 24 atom1059Coded := by decide +kernel
theorem atom1059Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99775826841600 : Int) atom1059Coded) := by
  have h := atom1059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1060 : SparsePolynomial.Poly := [([3,4,16], 1)]
theorem eval_atom1060 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1060 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1060_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72699192115200 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060Coded : CoefficientMerge.Poly := [(1840, 1)]
theorem atom1060Coded_decode : atom1060 = SparsePolynomial.decodeCubic 24 atom1060Coded := by decide +kernel
theorem atom1060Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72699192115200 : Int) atom1060Coded) := by
  have h := atom1060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1061 : SparsePolynomial.Poly := [([3,4,17], 1)]
theorem eval_atom1061 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1061 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1061_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70135468300800 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061Coded : CoefficientMerge.Poly := [(1841, 1)]
theorem atom1061Coded_decode : atom1061 = SparsePolynomial.decodeCubic 24 atom1061Coded := by decide +kernel
theorem atom1061Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (70135468300800 : Int) atom1061Coded) := by
  have h := atom1061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1062 : SparsePolynomial.Poly := [([3,4,18], 1)]
theorem eval_atom1062 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1062 = ((g 3) * (g 4) * (g 18)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1062_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117538264166400 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062Coded : CoefficientMerge.Poly := [(1842, 1)]
theorem atom1062Coded_decode : atom1062 = SparsePolynomial.decodeCubic 24 atom1062Coded := by decide +kernel
theorem atom1062Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (117538264166400 : Int) atom1062Coded) := by
  have h := atom1062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1063 : SparsePolynomial.Poly := [([3,4,19], 1)]
theorem eval_atom1063 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1063 = ((g 3) * (g 4) * (g 19)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1063_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58037916686400 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063Coded : CoefficientMerge.Poly := [(1843, 1)]
theorem atom1063Coded_decode : atom1063 = SparsePolynomial.decodeCubic 24 atom1063Coded := by decide +kernel
theorem atom1063Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58037916686400 : Int) atom1063Coded) := by
  have h := atom1063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1064 : SparsePolynomial.Poly := [([3,4,20], 1)]
theorem eval_atom1064 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1064 = ((g 3) * (g 4) * (g 20)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1064_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101760876504000 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064Coded : CoefficientMerge.Poly := [(1844, 1)]
theorem atom1064Coded_decode : atom1064 = SparsePolynomial.decodeCubic 24 atom1064Coded := by decide +kernel
theorem atom1064Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101760876504000 : Int) atom1064Coded) := by
  have h := atom1064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1065 : SparsePolynomial.Poly := [([3,4,21], 1)]
theorem eval_atom1065 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1065 = ((g 3) * (g 4) * (g 21)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1065_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77175480312000 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065Coded : CoefficientMerge.Poly := [(1845, 1)]
theorem atom1065Coded_decode : atom1065 = SparsePolynomial.decodeCubic 24 atom1065Coded := by decide +kernel
theorem atom1065Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77175480312000 : Int) atom1065Coded) := by
  have h := atom1065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1066 : SparsePolynomial.Poly := [([3,4,22], 1)]
theorem eval_atom1066 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1066 = ((g 3) * (g 4) * (g 22)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1066_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88906175870400 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066Coded : CoefficientMerge.Poly := [(1846, 1)]
theorem atom1066Coded_decode : atom1066 = SparsePolynomial.decodeCubic 24 atom1066Coded := by decide +kernel
theorem atom1066Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88906175870400 : Int) atom1066Coded) := by
  have h := atom1066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1067 : SparsePolynomial.Poly := [([3,4,23], 1)]
theorem eval_atom1067 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1067 = ((g 3) * (g 4) * (g 23)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1067_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100636871428800 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067Coded : CoefficientMerge.Poly := [(1847, 1)]
theorem atom1067Coded_decode : atom1067 = SparsePolynomial.decodeCubic 24 atom1067Coded := by decide +kernel
theorem atom1067Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100636871428800 : Int) atom1067Coded) := by
  have h := atom1067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1068 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom1068 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1068 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1068_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74737156032000 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068Coded : CoefficientMerge.Poly := [(1853, 1)]
theorem atom1068Coded_decode : atom1068 = SparsePolynomial.decodeCubic 24 atom1068Coded := by decide +kernel
theorem atom1068Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (74737156032000 : Int) atom1068Coded) := by
  have h := atom1068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1069 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom1069 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1069 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1069_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113960122204896 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069Coded : CoefficientMerge.Poly := [(1854, 1)]
theorem atom1069Coded_decode : atom1069 = SparsePolynomial.decodeCubic 24 atom1069Coded := by decide +kernel
theorem atom1069Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (113960122204896 : Int) atom1069Coded) := by
  have h := atom1069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1070 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom1070 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1070 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1070_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88220867740896 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070Coded : CoefficientMerge.Poly := [(1855, 1)]
theorem atom1070Coded_decode : atom1070 = SparsePolynomial.decodeCubic 24 atom1070Coded := by decide +kernel
theorem atom1070Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88220867740896 : Int) atom1070Coded) := by
  have h := atom1070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1071 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom1071 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1071 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1071_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87041908809504 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071Coded : CoefficientMerge.Poly := [(1856, 1)]
theorem atom1071Coded_decode : atom1071 = SparsePolynomial.decodeCubic 24 atom1071Coded := by decide +kernel
theorem atom1071Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87041908809504 : Int) atom1071Coded) := by
  have h := atom1071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1072 : SparsePolynomial.Poly := [([3,5,9], 1)]
theorem eval_atom1072 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1072 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1072_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91182603161232 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072Coded : CoefficientMerge.Poly := [(1857, 1)]
theorem atom1072Coded_decode : atom1072 = SparsePolynomial.decodeCubic 24 atom1072Coded := by decide +kernel
theorem atom1072Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91182603161232 : Int) atom1072Coded) := by
  have h := atom1072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1073 : SparsePolynomial.Poly := [([3,5,10], 1)]
theorem eval_atom1073 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1073 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1073_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102037343565168 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073Coded : CoefficientMerge.Poly := [(1858, 1)]
theorem atom1073Coded_decode : atom1073 = SparsePolynomial.decodeCubic 24 atom1073Coded := by decide +kernel
theorem atom1073Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102037343565168 : Int) atom1073Coded) := by
  have h := atom1073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1074 : SparsePolynomial.Poly := [([3,5,11], 1)]
theorem eval_atom1074 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1074 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1074_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119621894534208 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074Coded : CoefficientMerge.Poly := [(1859, 1)]
theorem atom1074Coded_decode : atom1074 = SparsePolynomial.decodeCubic 24 atom1074Coded := by decide +kernel
theorem atom1074Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (119621894534208 : Int) atom1074Coded) := by
  have h := atom1074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1075 : SparsePolynomial.Poly := [([3,5,12], 1)]
theorem eval_atom1075 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1075 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1075_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171213389221248 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075Coded : CoefficientMerge.Poly := [(1860, 1)]
theorem atom1075Coded_decode : atom1075 = SparsePolynomial.decodeCubic 24 atom1075Coded := by decide +kernel
theorem atom1075Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171213389221248 : Int) atom1075Coded) := by
  have h := atom1075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1076 : SparsePolynomial.Poly := [([3,5,13], 1)]
theorem eval_atom1076 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1076 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1076_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149638658400000 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076Coded : CoefficientMerge.Poly := [(1861, 1)]
theorem atom1076Coded_decode : atom1076 = SparsePolynomial.decodeCubic 24 atom1076Coded := by decide +kernel
theorem atom1076Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149638658400000 : Int) atom1076Coded) := by
  have h := atom1076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1077 : SparsePolynomial.Poly := [([3,5,14], 1)]
theorem eval_atom1077 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1077 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1077_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120715401945600 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077Coded : CoefficientMerge.Poly := [(1862, 1)]
theorem atom1077Coded_decode : atom1077 = SparsePolynomial.decodeCubic 24 atom1077Coded := by decide +kernel
theorem atom1077Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (120715401945600 : Int) atom1077Coded) := by
  have h := atom1077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1078 : SparsePolynomial.Poly := [([3,5,15], 1)]
theorem eval_atom1078 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1078 = ((g 3) * (g 5) * (g 15)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1078_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122103897753600 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078Coded : CoefficientMerge.Poly := [(1863, 1)]
theorem atom1078Coded_decode : atom1078 = SparsePolynomial.decodeCubic 24 atom1078Coded := by decide +kernel
theorem atom1078Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122103897753600 : Int) atom1078Coded) := by
  have h := atom1078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1079 : SparsePolynomial.Poly := [([3,5,16], 1)]
theorem eval_atom1079 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1079 = ((g 3) * (g 5) * (g 16)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1079_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111669883315200 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079Coded : CoefficientMerge.Poly := [(1864, 1)]
theorem atom1079Coded_decode : atom1079 = SparsePolynomial.decodeCubic 24 atom1079Coded := by decide +kernel
theorem atom1079Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111669883315200 : Int) atom1079Coded) := by
  have h := atom1079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1080 : SparsePolynomial.Poly := [([3,5,17], 1)]
theorem eval_atom1080 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1080 = ((g 3) * (g 5) * (g 17)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1080_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111168607334400 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080Coded : CoefficientMerge.Poly := [(1865, 1)]
theorem atom1080Coded_decode : atom1080 = SparsePolynomial.decodeCubic 24 atom1080Coded := by decide +kernel
theorem atom1080Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111168607334400 : Int) atom1080Coded) := by
  have h := atom1080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1081 : SparsePolynomial.Poly := [([3,5,18], 1)]
theorem eval_atom1081 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1081 = ((g 3) * (g 5) * (g 18)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1081_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151375708915200 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081Coded : CoefficientMerge.Poly := [(1866, 1)]
theorem atom1081Coded_decode : atom1081 = SparsePolynomial.decodeCubic 24 atom1081Coded := by decide +kernel
theorem atom1081Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151375708915200 : Int) atom1081Coded) := by
  have h := atom1081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1082 : SparsePolynomial.Poly := [([3,5,19], 1)]
theorem eval_atom1082 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1082 = ((g 3) * (g 5) * (g 19)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1082_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109815055257600 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082Coded : CoefficientMerge.Poly := [(1867, 1)]
theorem atom1082Coded_decode : atom1082 = SparsePolynomial.decodeCubic 24 atom1082Coded := by decide +kernel
theorem atom1082Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109815055257600 : Int) atom1082Coded) := by
  have h := atom1082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1083 : SparsePolynomial.Poly := [([3,5,20], 1)]
theorem eval_atom1083 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1083 = ((g 3) * (g 5) * (g 20)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1083_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (160013198822400 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083Coded : CoefficientMerge.Poly := [(1868, 1)]
theorem atom1083Coded_decode : atom1083 = SparsePolynomial.decodeCubic 24 atom1083Coded := by decide +kernel
theorem atom1083Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (160013198822400 : Int) atom1083Coded) := by
  have h := atom1083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1084 : SparsePolynomial.Poly := [([3,5,21], 1)]
theorem eval_atom1084 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1084 = ((g 3) * (g 5) * (g 21)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1084_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146315722291200 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084Coded : CoefficientMerge.Poly := [(1869, 1)]
theorem atom1084Coded_decode : atom1084 = SparsePolynomial.decodeCubic 24 atom1084Coded := by decide +kernel
theorem atom1084Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146315722291200 : Int) atom1084Coded) := by
  have h := atom1084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1085 : SparsePolynomial.Poly := [([3,5,22], 1)]
theorem eval_atom1085 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1085 = ((g 3) * (g 5) * (g 22)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1085_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168934337510400 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085Coded : CoefficientMerge.Poly := [(1870, 1)]
theorem atom1085Coded_decode : atom1085 = SparsePolynomial.decodeCubic 24 atom1085Coded := by decide +kernel
theorem atom1085Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168934337510400 : Int) atom1085Coded) := by
  have h := atom1085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1086 : SparsePolynomial.Poly := [([3,5,23], 1)]
theorem eval_atom1086 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1086 = ((g 3) * (g 5) * (g 23)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1086_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191552952729600 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086Coded : CoefficientMerge.Poly := [(1871, 1)]
theorem atom1086Coded_decode : atom1086 = SparsePolynomial.decodeCubic 24 atom1086Coded := by decide +kernel
theorem atom1086Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191552952729600 : Int) atom1086Coded) := by
  have h := atom1086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1087 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom1087 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1087 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1087_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75779011123200 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087Coded : CoefficientMerge.Poly := [(1878, 1)]
theorem atom1087Coded_decode : atom1087 = SparsePolynomial.decodeCubic 24 atom1087Coded := by decide +kernel
theorem atom1087Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75779011123200 : Int) atom1087Coded) := by
  have h := atom1087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1088 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom1088 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1088 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1088_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123777582297600 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088Coded : CoefficientMerge.Poly := [(1879, 1)]
theorem atom1088Coded_decode : atom1088 = SparsePolynomial.decodeCubic 24 atom1088Coded := by decide +kernel
theorem atom1088Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123777582297600 : Int) atom1088Coded) := by
  have h := atom1088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block015 : CoefficientMerge.Poly := [(1583, 475798210272000), (1602, 290294848166400), (1603, 476361662515200), (1604, 653817225600000), (1605, 549589191782400), (1606, 349197353164800), (1607, 503137604138400), (1627, 186615382947840), (1628, 534152726553600), (1629, 503407370188800), (1630, 347292762163200), (1631, 386611959333600), (1652, 348085912204800), (1653, 527646447820800), (1654, 345267040204800), (1655, 404881632540000), (1677, 170311413888000), (1678, 217123374182400), (1679, 288355987735200), (1702, 8846586806400), (1703, 100071607053600), (1727, 78422186858400), (1803, 23813830656000), (1804, 65232886118400), (1805, 65907174009600), (1806, 52815674419200), (1807, 46607068569600), (1808, 40398462720000), (1809, 40201637916528), (1810, 51636529101168), (1811, 61432993046304), (1812, 83146369420224), (1813, 68276633040000), (1814, 49732633843200), (1815, 45975641241600), (1816, 30396138393600), (1817, 24749374003200), (1818, 48733303449600), (1820, 36316091750400), (1828, 63987427929600), (1829, 107581417564896), (1830, 76714554470400), (1831, 68379713740800), (1832, 60044873011200), (1833, 63733594373856), (1834, 90685747712736), (1835, 114361046572608), (1836, 161870170290048), (1837, 136213068499200), (1838, 103207441075200), (1839, 99775826841600), (1840, 72699192115200), (1841, 70135468300800), (1842, 117538264166400), (1843, 58037916686400), (1844, 101760876504000), (1845, 77175480312000), (1846, 88906175870400), (1847, 100636871428800), (1853, 74737156032000), (1854, 113960122204896), (1855, 88220867740896), (1856, 87041908809504), (1857, 91182603161232), (1858, 102037343565168), (1859, 119621894534208), (1860, 171213389221248), (1861, 149638658400000), (1862, 120715401945600), (1863, 122103897753600), (1864, 111669883315200), (1865, 111168607334400), (1866, 151375708915200), (1867, 109815055257600), (1868, 160013198822400), (1869, 146315722291200), (1870, 168934337510400), (1871, 191552952729600), (1878, 75779011123200), (1879, 123777582297600)]
theorem block015_data : block015 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (475798210272000 : Int) atom1009Coded) (CoefficientMerge.scale (290294848166400 : Int) atom1010Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (476361662515200 : Int) atom1011Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (653817225600000 : Int) atom1012Coded) (CoefficientMerge.scale (549589191782400 : Int) atom1013Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (349197353164800 : Int) atom1014Coded) (CoefficientMerge.scale (503137604138400 : Int) atom1015Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186615382947840 : Int) atom1016Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (534152726553600 : Int) atom1017Coded) (CoefficientMerge.scale (503407370188800 : Int) atom1018Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (347292762163200 : Int) atom1019Coded) (CoefficientMerge.scale (386611959333600 : Int) atom1020Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348085912204800 : Int) atom1021Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (527646447820800 : Int) atom1022Coded) (CoefficientMerge.scale (345267040204800 : Int) atom1023Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (404881632540000 : Int) atom1024Coded) (CoefficientMerge.scale (170311413888000 : Int) atom1025Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217123374182400 : Int) atom1026Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (288355987735200 : Int) atom1027Coded) (CoefficientMerge.scale (8846586806400 : Int) atom1028Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (100071607053600 : Int) atom1029Coded) (CoefficientMerge.scale (78422186858400 : Int) atom1030Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23813830656000 : Int) atom1031Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65232886118400 : Int) atom1032Coded) (CoefficientMerge.scale (65907174009600 : Int) atom1033Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52815674419200 : Int) atom1034Coded) (CoefficientMerge.scale (46607068569600 : Int) atom1035Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40398462720000 : Int) atom1036Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40201637916528 : Int) atom1037Coded) (CoefficientMerge.scale (51636529101168 : Int) atom1038Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61432993046304 : Int) atom1039Coded) (CoefficientMerge.scale (83146369420224 : Int) atom1040Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68276633040000 : Int) atom1041Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49732633843200 : Int) atom1042Coded) (CoefficientMerge.scale (45975641241600 : Int) atom1043Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30396138393600 : Int) atom1044Coded) (CoefficientMerge.scale (24749374003200 : Int) atom1045Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48733303449600 : Int) atom1046Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36316091750400 : Int) atom1047Coded) (CoefficientMerge.scale (63987427929600 : Int) atom1048Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (107581417564896 : Int) atom1049Coded) (CoefficientMerge.scale (76714554470400 : Int) atom1050Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68379713740800 : Int) atom1051Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60044873011200 : Int) atom1052Coded) (CoefficientMerge.scale (63733594373856 : Int) atom1053Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90685747712736 : Int) atom1054Coded) (CoefficientMerge.scale (114361046572608 : Int) atom1055Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161870170290048 : Int) atom1056Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136213068499200 : Int) atom1057Coded) (CoefficientMerge.scale (103207441075200 : Int) atom1058Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99775826841600 : Int) atom1059Coded) (CoefficientMerge.scale (72699192115200 : Int) atom1060Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70135468300800 : Int) atom1061Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117538264166400 : Int) atom1062Coded) (CoefficientMerge.scale (58037916686400 : Int) atom1063Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101760876504000 : Int) atom1064Coded) (CoefficientMerge.scale (77175480312000 : Int) atom1065Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88906175870400 : Int) atom1066Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (100636871428800 : Int) atom1067Coded) (CoefficientMerge.scale (74737156032000 : Int) atom1068Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (113960122204896 : Int) atom1069Coded) (CoefficientMerge.scale (88220867740896 : Int) atom1070Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87041908809504 : Int) atom1071Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91182603161232 : Int) atom1072Coded) (CoefficientMerge.scale (102037343565168 : Int) atom1073Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119621894534208 : Int) atom1074Coded) (CoefficientMerge.scale (171213389221248 : Int) atom1075Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149638658400000 : Int) atom1076Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120715401945600 : Int) atom1077Coded) (CoefficientMerge.scale (122103897753600 : Int) atom1078Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111669883315200 : Int) atom1079Coded) (CoefficientMerge.scale (111168607334400 : Int) atom1080Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (151375708915200 : Int) atom1081Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109815055257600 : Int) atom1082Coded) (CoefficientMerge.scale (160013198822400 : Int) atom1083Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146315722291200 : Int) atom1084Coded) (CoefficientMerge.scale (168934337510400 : Int) atom1085Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191552952729600 : Int) atom1086Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (75779011123200 : Int) atom1087Coded) (CoefficientMerge.scale (123777582297600 : Int) atom1088Coded)))))))) := by decide +kernel
theorem block015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block015 := by
  rw [block015_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1009Coded_nonneg g hg hA hB) (atom1010Coded_nonneg g hg hA hB)) (add_nonneg (atom1011Coded_nonneg g hg hA hB) (add_nonneg (atom1012Coded_nonneg g hg hA hB) (atom1013Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1014Coded_nonneg g hg hA hB) (atom1015Coded_nonneg g hg hA hB)) (add_nonneg (atom1016Coded_nonneg g hg hA hB) (add_nonneg (atom1017Coded_nonneg g hg hA hB) (atom1018Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1019Coded_nonneg g hg hA hB) (atom1020Coded_nonneg g hg hA hB)) (add_nonneg (atom1021Coded_nonneg g hg hA hB) (add_nonneg (atom1022Coded_nonneg g hg hA hB) (atom1023Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1024Coded_nonneg g hg hA hB) (atom1025Coded_nonneg g hg hA hB)) (add_nonneg (atom1026Coded_nonneg g hg hA hB) (add_nonneg (atom1027Coded_nonneg g hg hA hB) (atom1028Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1029Coded_nonneg g hg hA hB) (atom1030Coded_nonneg g hg hA hB)) (add_nonneg (atom1031Coded_nonneg g hg hA hB) (add_nonneg (atom1032Coded_nonneg g hg hA hB) (atom1033Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1034Coded_nonneg g hg hA hB) (atom1035Coded_nonneg g hg hA hB)) (add_nonneg (atom1036Coded_nonneg g hg hA hB) (add_nonneg (atom1037Coded_nonneg g hg hA hB) (atom1038Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1039Coded_nonneg g hg hA hB) (atom1040Coded_nonneg g hg hA hB)) (add_nonneg (atom1041Coded_nonneg g hg hA hB) (add_nonneg (atom1042Coded_nonneg g hg hA hB) (atom1043Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1044Coded_nonneg g hg hA hB) (atom1045Coded_nonneg g hg hA hB)) (add_nonneg (atom1046Coded_nonneg g hg hA hB) (add_nonneg (atom1047Coded_nonneg g hg hA hB) (atom1048Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1049Coded_nonneg g hg hA hB) (atom1050Coded_nonneg g hg hA hB)) (add_nonneg (atom1051Coded_nonneg g hg hA hB) (add_nonneg (atom1052Coded_nonneg g hg hA hB) (atom1053Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1054Coded_nonneg g hg hA hB) (atom1055Coded_nonneg g hg hA hB)) (add_nonneg (atom1056Coded_nonneg g hg hA hB) (add_nonneg (atom1057Coded_nonneg g hg hA hB) (atom1058Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1059Coded_nonneg g hg hA hB) (atom1060Coded_nonneg g hg hA hB)) (add_nonneg (atom1061Coded_nonneg g hg hA hB) (add_nonneg (atom1062Coded_nonneg g hg hA hB) (atom1063Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1064Coded_nonneg g hg hA hB) (atom1065Coded_nonneg g hg hA hB)) (add_nonneg (atom1066Coded_nonneg g hg hA hB) (add_nonneg (atom1067Coded_nonneg g hg hA hB) (atom1068Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1069Coded_nonneg g hg hA hB) (atom1070Coded_nonneg g hg hA hB)) (add_nonneg (atom1071Coded_nonneg g hg hA hB) (add_nonneg (atom1072Coded_nonneg g hg hA hB) (atom1073Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1074Coded_nonneg g hg hA hB) (atom1075Coded_nonneg g hg hA hB)) (add_nonneg (atom1076Coded_nonneg g hg hA hB) (add_nonneg (atom1077Coded_nonneg g hg hA hB) (atom1078Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1079Coded_nonneg g hg hA hB) (atom1080Coded_nonneg g hg hA hB)) (add_nonneg (atom1081Coded_nonneg g hg hA hB) (add_nonneg (atom1082Coded_nonneg g hg hA hB) (atom1083Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1084Coded_nonneg g hg hA hB) (atom1085Coded_nonneg g hg hA hB)) (add_nonneg (atom1086Coded_nonneg g hg hA hB) (add_nonneg (atom1087Coded_nonneg g hg hA hB) (atom1088Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
