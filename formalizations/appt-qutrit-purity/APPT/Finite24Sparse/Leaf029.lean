import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2129 : SparsePolynomial.Poly := [([10,11,23], 1)]
theorem eval_atom2129 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2129 = ((g 10) * (g 11) * (g 23)) := by
  norm_num [atom2129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2129_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144759386217600 : Int) atom2129) := by
  rw [SparsePolynomial.eval_scale, eval_atom2129]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2129Coded : CoefficientMerge.Poly := [(6047, 1)]
theorem atom2129Coded_decode : atom2129 = SparsePolynomial.decodeCubic 24 atom2129Coded := by decide +kernel
theorem atom2129Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) := by
  have h := atom2129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2130 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom2130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2130 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom2130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171370949200 : Int) atom2130) := by
  rw [SparsePolynomial.eval_scale, eval_atom2130]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2130Coded : CoefficientMerge.Poly := [(6060, 1)]
theorem atom2130Coded_decode : atom2130 = SparsePolynomial.decodeCubic 24 atom2130Coded := by decide +kernel
theorem atom2130Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded) := by
  have h := atom2130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2131 : SparsePolynomial.Poly := [([10,12,13], 1)]
theorem eval_atom2131 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2131 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom2131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2131_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15674337756000 : Int) atom2131) := by
  rw [SparsePolynomial.eval_scale, eval_atom2131]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2131Coded : CoefficientMerge.Poly := [(6061, 1)]
theorem atom2131Coded_decode : atom2131 = SparsePolynomial.decodeCubic 24 atom2131Coded := by decide +kernel
theorem atom2131Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) := by
  have h := atom2131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2132 : SparsePolynomial.Poly := [([10,12,14], 1)]
theorem eval_atom2132 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2132 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom2132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2132_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20819826165600 : Int) atom2132) := by
  rw [SparsePolynomial.eval_scale, eval_atom2132]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2132Coded : CoefficientMerge.Poly := [(6062, 1)]
theorem atom2132Coded_decode : atom2132 = SparsePolynomial.decodeCubic 24 atom2132Coded := by decide +kernel
theorem atom2132Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) := by
  have h := atom2132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2133 : SparsePolynomial.Poly := [([10,12,15], 1)]
theorem eval_atom2133 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2133 = ((g 10) * (g 12) * (g 15)) := by
  norm_num [atom2133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2133_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25965314575200 : Int) atom2133) := by
  rw [SparsePolynomial.eval_scale, eval_atom2133]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2133Coded : CoefficientMerge.Poly := [(6063, 1)]
theorem atom2133Coded_decode : atom2133 = SparsePolynomial.decodeCubic 24 atom2133Coded := by decide +kernel
theorem atom2133Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded) := by
  have h := atom2133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2134 : SparsePolynomial.Poly := [([10,12,16], 1)]
theorem eval_atom2134 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2134 = ((g 10) * (g 12) * (g 16)) := by
  norm_num [atom2134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2134_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31110802984800 : Int) atom2134) := by
  rw [SparsePolynomial.eval_scale, eval_atom2134]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2134Coded : CoefficientMerge.Poly := [(6064, 1)]
theorem atom2134Coded_decode : atom2134 = SparsePolynomial.decodeCubic 24 atom2134Coded := by decide +kernel
theorem atom2134Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) := by
  have h := atom2134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2135 : SparsePolynomial.Poly := [([10,12,17], 1)]
theorem eval_atom2135 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2135 = ((g 10) * (g 12) * (g 17)) := by
  norm_num [atom2135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2135_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36256291394400 : Int) atom2135) := by
  rw [SparsePolynomial.eval_scale, eval_atom2135]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2135Coded : CoefficientMerge.Poly := [(6065, 1)]
theorem atom2135Coded_decode : atom2135 = SparsePolynomial.decodeCubic 24 atom2135Coded := by decide +kernel
theorem atom2135Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded) := by
  have h := atom2135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2136 : SparsePolynomial.Poly := [([10,12,18], 1)]
theorem eval_atom2136 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2136 = ((g 10) * (g 12) * (g 18)) := by
  norm_num [atom2136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2136_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45334222105392 : Int) atom2136) := by
  rw [SparsePolynomial.eval_scale, eval_atom2136]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2136Coded : CoefficientMerge.Poly := [(6066, 1)]
theorem atom2136Coded_decode : atom2136 = SparsePolynomial.decodeCubic 24 atom2136Coded := by decide +kernel
theorem atom2136Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) := by
  have h := atom2136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2137 : SparsePolynomial.Poly := [([10,12,20], 1)]
theorem eval_atom2137 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2137 = ((g 10) * (g 12) * (g 20)) := by
  norm_num [atom2137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2137_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62475180994512 : Int) atom2137) := by
  rw [SparsePolynomial.eval_scale, eval_atom2137]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2137Coded : CoefficientMerge.Poly := [(6068, 1)]
theorem atom2137Coded_decode : atom2137 = SparsePolynomial.decodeCubic 24 atom2137Coded := by decide +kernel
theorem atom2137Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) := by
  have h := atom2137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2138 : SparsePolynomial.Poly := [([10,12,21], 1)]
theorem eval_atom2138 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2138 = ((g 10) * (g 12) * (g 21)) := by
  norm_num [atom2138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2138_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74122873486200 : Int) atom2138) := by
  rw [SparsePolynomial.eval_scale, eval_atom2138]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2138Coded : CoefficientMerge.Poly := [(6069, 1)]
theorem atom2138Coded_decode : atom2138 = SparsePolynomial.decodeCubic 24 atom2138Coded := by decide +kernel
theorem atom2138Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded) := by
  have h := atom2138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2139 : SparsePolynomial.Poly := [([10,12,22], 1)]
theorem eval_atom2139 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2139 = ((g 10) * (g 12) * (g 22)) := by
  norm_num [atom2139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2139_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153208246292640 : Int) atom2139) := by
  rw [SparsePolynomial.eval_scale, eval_atom2139]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2139Coded : CoefficientMerge.Poly := [(6070, 1)]
theorem atom2139Coded_decode : atom2139 = SparsePolynomial.decodeCubic 24 atom2139Coded := by decide +kernel
theorem atom2139Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) := by
  have h := atom2139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2140 : SparsePolynomial.Poly := [([10,12,23], 1)]
theorem eval_atom2140 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2140 = ((g 10) * (g 12) * (g 23)) := by
  norm_num [atom2140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2140_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (247986262408500 : Int) atom2140) := by
  rw [SparsePolynomial.eval_scale, eval_atom2140]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2140Coded : CoefficientMerge.Poly := [(6071, 1)]
theorem atom2140Coded_decode : atom2140 = SparsePolynomial.decodeCubic 24 atom2140Coded := by decide +kernel
theorem atom2140Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded) := by
  have h := atom2140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2141 : SparsePolynomial.Poly := [([10,13,13], 1)]
theorem eval_atom2141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2141 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom2141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27104843581200 : Int) atom2141) := by
  rw [SparsePolynomial.eval_scale, eval_atom2141]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2141Coded : CoefficientMerge.Poly := [(6085, 1)]
theorem atom2141Coded_decode : atom2141 = SparsePolynomial.decodeCubic 24 atom2141Coded := by decide +kernel
theorem atom2141Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) := by
  have h := atom2141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2142 : SparsePolynomial.Poly := [([10,13,14], 1)]
theorem eval_atom2142 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2142 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom2142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2142_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48070183946400 : Int) atom2142) := by
  rw [SparsePolynomial.eval_scale, eval_atom2142]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2142Coded : CoefficientMerge.Poly := [(6086, 1)]
theorem atom2142Coded_decode : atom2142 = SparsePolynomial.decodeCubic 24 atom2142Coded := by decide +kernel
theorem atom2142Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) := by
  have h := atom2142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2143 : SparsePolynomial.Poly := [([10,13,15], 1)]
theorem eval_atom2143 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2143 = ((g 10) * (g 13) * (g 15)) := by
  norm_num [atom2143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2143_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51174486871200 : Int) atom2143) := by
  rw [SparsePolynomial.eval_scale, eval_atom2143]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2143Coded : CoefficientMerge.Poly := [(6087, 1)]
theorem atom2143Coded_decode : atom2143 = SparsePolynomial.decodeCubic 24 atom2143Coded := by decide +kernel
theorem atom2143Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded) := by
  have h := atom2143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2144 : SparsePolynomial.Poly := [([10,13,16], 1)]
theorem eval_atom2144 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2144 = ((g 10) * (g 13) * (g 16)) := by
  norm_num [atom2144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2144_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57361830372000 : Int) atom2144) := by
  rw [SparsePolynomial.eval_scale, eval_atom2144]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2144Coded : CoefficientMerge.Poly := [(6088, 1)]
theorem atom2144Coded_decode : atom2144 = SparsePolynomial.decodeCubic 24 atom2144Coded := by decide +kernel
theorem atom2144Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) := by
  have h := atom2144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2145 : SparsePolynomial.Poly := [([10,13,17], 1)]
theorem eval_atom2145 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2145 = ((g 10) * (g 13) * (g 17)) := by
  norm_num [atom2145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2145_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63549173872800 : Int) atom2145) := by
  rw [SparsePolynomial.eval_scale, eval_atom2145]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2145Coded : CoefficientMerge.Poly := [(6089, 1)]
theorem atom2145Coded_decode : atom2145 = SparsePolynomial.decodeCubic 24 atom2145Coded := by decide +kernel
theorem atom2145Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded) := by
  have h := atom2145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2146 : SparsePolynomial.Poly := [([10,13,18], 1)]
theorem eval_atom2146 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2146 = ((g 10) * (g 13) * (g 18)) := by
  norm_num [atom2146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2146_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73075050903888 : Int) atom2146) := by
  rw [SparsePolynomial.eval_scale, eval_atom2146]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2146Coded : CoefficientMerge.Poly := [(6090, 1)]
theorem atom2146Coded_decode : atom2146 = SparsePolynomial.decodeCubic 24 atom2146Coded := by decide +kernel
theorem atom2146Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) := by
  have h := atom2146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2147 : SparsePolynomial.Poly := [([10,13,19], 1)]
theorem eval_atom2147 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2147 = ((g 10) * (g 13) * (g 19)) := by
  norm_num [atom2147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2147_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42531469390080 : Int) atom2147) := by
  rw [SparsePolynomial.eval_scale, eval_atom2147]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2147Coded : CoefficientMerge.Poly := [(6091, 1)]
theorem atom2147Coded_decode : atom2147 = SparsePolynomial.decodeCubic 24 atom2147Coded := by decide +kernel
theorem atom2147Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) := by
  have h := atom2147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2148 : SparsePolynomial.Poly := [([10,13,20], 1)]
theorem eval_atom2148 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2148 = ((g 10) * (g 13) * (g 20)) := by
  norm_num [atom2148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2148_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123990436996272 : Int) atom2148) := by
  rw [SparsePolynomial.eval_scale, eval_atom2148]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2148Coded : CoefficientMerge.Poly := [(6092, 1)]
theorem atom2148Coded_decode : atom2148 = SparsePolynomial.decodeCubic 24 atom2148Coded := by decide +kernel
theorem atom2148Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded) := by
  have h := atom2148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2149 : SparsePolynomial.Poly := [([10,13,21], 1)]
theorem eval_atom2149 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2149 = ((g 10) * (g 13) * (g 21)) := by
  norm_num [atom2149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2149_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139283462035080 : Int) atom2149) := by
  rw [SparsePolynomial.eval_scale, eval_atom2149]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2149Coded : CoefficientMerge.Poly := [(6093, 1)]
theorem atom2149Coded_decode : atom2149 = SparsePolynomial.decodeCubic 24 atom2149Coded := by decide +kernel
theorem atom2149Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) := by
  have h := atom2149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2150 : SparsePolynomial.Poly := [([10,13,22], 1)]
theorem eval_atom2150 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2150 = ((g 10) * (g 13) * (g 22)) := by
  norm_num [atom2150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2150_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231954760353888 : Int) atom2150) := by
  rw [SparsePolynomial.eval_scale, eval_atom2150]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2150Coded : CoefficientMerge.Poly := [(6094, 1)]
theorem atom2150Coded_decode : atom2150 = SparsePolynomial.decodeCubic 24 atom2150Coded := by decide +kernel
theorem atom2150Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded) := by
  have h := atom2150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2151 : SparsePolynomial.Poly := [([10,13,23], 1)]
theorem eval_atom2151 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2151 = ((g 10) * (g 13) * (g 23)) := by
  norm_num [atom2151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2151_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (339742267533900 : Int) atom2151) := by
  rw [SparsePolynomial.eval_scale, eval_atom2151]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2151Coded : CoefficientMerge.Poly := [(6095, 1)]
theorem atom2151Coded_decode : atom2151 = SparsePolynomial.decodeCubic 24 atom2151Coded := by decide +kernel
theorem atom2151Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) := by
  have h := atom2151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2152 : SparsePolynomial.Poly := [([10,14,14], 1)]
theorem eval_atom2152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2152 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom2152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43567217139600 : Int) atom2152) := by
  rw [SparsePolynomial.eval_scale, eval_atom2152]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2152Coded : CoefficientMerge.Poly := [(6110, 1)]
theorem atom2152Coded_decode : atom2152 = SparsePolynomial.decodeCubic 24 atom2152Coded := by decide +kernel
theorem atom2152Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) := by
  have h := atom2152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2153 : SparsePolynomial.Poly := [([10,14,15], 1)]
theorem eval_atom2153 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2153 = ((g 10) * (g 14) * (g 15)) := by
  norm_num [atom2153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2153_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85125142317600 : Int) atom2153) := by
  rw [SparsePolynomial.eval_scale, eval_atom2153]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2153Coded : CoefficientMerge.Poly := [(6111, 1)]
theorem atom2153Coded_decode : atom2153 = SparsePolynomial.decodeCubic 24 atom2153Coded := by decide +kernel
theorem atom2153Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded) := by
  have h := atom2153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2154 : SparsePolynomial.Poly := [([10,14,16], 1)]
theorem eval_atom2154 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2154 = ((g 10) * (g 14) * (g 16)) := by
  norm_num [atom2154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2154_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91333748167200 : Int) atom2154) := by
  rw [SparsePolynomial.eval_scale, eval_atom2154]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2154Coded : CoefficientMerge.Poly := [(6112, 1)]
theorem atom2154Coded_decode : atom2154 = SparsePolynomial.decodeCubic 24 atom2154Coded := by decide +kernel
theorem atom2154Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) := by
  have h := atom2154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2155 : SparsePolynomial.Poly := [([10,14,17], 1)]
theorem eval_atom2155 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2155 = ((g 10) * (g 14) * (g 17)) := by
  norm_num [atom2155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2155_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97542354016800 : Int) atom2155) := by
  rw [SparsePolynomial.eval_scale, eval_atom2155]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2155Coded : CoefficientMerge.Poly := [(6113, 1)]
theorem atom2155Coded_decode : atom2155 = SparsePolynomial.decodeCubic 24 atom2155Coded := by decide +kernel
theorem atom2155Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded) := by
  have h := atom2155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2156 : SparsePolynomial.Poly := [([10,14,18], 1)]
theorem eval_atom2156 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2156 = ((g 10) * (g 14) * (g 18)) := by
  norm_num [atom2156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2156_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98659441119888 : Int) atom2156) := by
  rw [SparsePolynomial.eval_scale, eval_atom2156]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2156Coded : CoefficientMerge.Poly := [(6114, 1)]
theorem atom2156Coded_decode : atom2156 = SparsePolynomial.decodeCubic 24 atom2156Coded := by decide +kernel
theorem atom2156Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) := by
  have h := atom2156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2157 : SparsePolynomial.Poly := [([10,14,19], 1)]
theorem eval_atom2157 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2157 = ((g 10) * (g 14) * (g 19)) := by
  norm_num [atom2157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2157_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89005622222880 : Int) atom2157) := by
  rw [SparsePolynomial.eval_scale, eval_atom2157]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2157Coded : CoefficientMerge.Poly := [(6115, 1)]
theorem atom2157Coded_decode : atom2157 = SparsePolynomial.decodeCubic 24 atom2157Coded := by decide +kernel
theorem atom2157Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) := by
  have h := atom2157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2158 : SparsePolynomial.Poly := [([10,14,20], 1)]
theorem eval_atom2158 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2158 = ((g 10) * (g 14) * (g 20)) := by
  norm_num [atom2158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2158_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181911628693872 : Int) atom2158) := by
  rw [SparsePolynomial.eval_scale, eval_atom2158]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2158Coded : CoefficientMerge.Poly := [(6116, 1)]
theorem atom2158Coded_decode : atom2158 = SparsePolynomial.decodeCubic 24 atom2158Coded := by decide +kernel
theorem atom2158Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded) := by
  have h := atom2158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2159 : SparsePolynomial.Poly := [([10,14,21], 1)]
theorem eval_atom2159 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2159 = ((g 10) * (g 14) * (g 21)) := by
  norm_num [atom2159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2159_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210902114186280 : Int) atom2159) := by
  rw [SparsePolynomial.eval_scale, eval_atom2159]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2159Coded : CoefficientMerge.Poly := [(6117, 1)]
theorem atom2159Coded_decode : atom2159 = SparsePolynomial.decodeCubic 24 atom2159Coded := by decide +kernel
theorem atom2159Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) := by
  have h := atom2159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2160 : SparsePolynomial.Poly := [([10,14,22], 1)]
theorem eval_atom2160 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2160 = ((g 10) * (g 14) * (g 22)) := by
  norm_num [atom2160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2160_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296892084189888 : Int) atom2160) := by
  rw [SparsePolynomial.eval_scale, eval_atom2160]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2160Coded : CoefficientMerge.Poly := [(6118, 1)]
theorem atom2160Coded_decode : atom2160 = SparsePolynomial.decodeCubic 24 atom2160Coded := by decide +kernel
theorem atom2160Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded) := by
  have h := atom2160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2161 : SparsePolynomial.Poly := [([10,14,23], 1)]
theorem eval_atom2161 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2161 = ((g 10) * (g 14) * (g 23)) := by
  norm_num [atom2161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2161_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (409342572985500 : Int) atom2161) := by
  rw [SparsePolynomial.eval_scale, eval_atom2161]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2161Coded : CoefficientMerge.Poly := [(6119, 1)]
theorem atom2161Coded_decode : atom2161 = SparsePolynomial.decodeCubic 24 atom2161Coded := by decide +kernel
theorem atom2161Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) := by
  have h := atom2161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2162 : SparsePolynomial.Poly := [([10,15,15], 1)]
theorem eval_atom2162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2162 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom2162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67242842528400 : Int) atom2162) := by
  rw [SparsePolynomial.eval_scale, eval_atom2162]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2162Coded : CoefficientMerge.Poly := [(6135, 1)]
theorem atom2162Coded_decode : atom2162 = SparsePolynomial.decodeCubic 24 atom2162Coded := by decide +kernel
theorem atom2162Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) := by
  have h := atom2162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2163 : SparsePolynomial.Poly := [([10,15,16], 1)]
theorem eval_atom2163 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2163 = ((g 10) * (g 15) * (g 16)) := by
  norm_num [atom2163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2163_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126342205466400 : Int) atom2163) := by
  rw [SparsePolynomial.eval_scale, eval_atom2163]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2163Coded : CoefficientMerge.Poly := [(6136, 1)]
theorem atom2163Coded_decode : atom2163 = SparsePolynomial.decodeCubic 24 atom2163Coded := by decide +kernel
theorem atom2163Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded) := by
  have h := atom2163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2164 : SparsePolynomial.Poly := [([10,15,17], 1)]
theorem eval_atom2164 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2164 = ((g 10) * (g 15) * (g 17)) := by
  norm_num [atom2164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2164_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131551480922400 : Int) atom2164) := by
  rw [SparsePolynomial.eval_scale, eval_atom2164]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2164Coded : CoefficientMerge.Poly := [(6137, 1)]
theorem atom2164Coded_decode : atom2164 = SparsePolynomial.decodeCubic 24 atom2164Coded := by decide +kernel
theorem atom2164Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) := by
  have h := atom2164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2165 : SparsePolynomial.Poly := [([10,15,18], 1)]
theorem eval_atom2165 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2165 = ((g 10) * (g 15) * (g 18)) := by
  norm_num [atom2165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2165_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146424341228688 : Int) atom2165) := by
  rw [SparsePolynomial.eval_scale, eval_atom2165]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2165Coded : CoefficientMerge.Poly := [(6138, 1)]
theorem atom2165Coded_decode : atom2165 = SparsePolynomial.decodeCubic 24 atom2165Coded := by decide +kernel
theorem atom2165Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded) := by
  have h := atom2165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2166 : SparsePolynomial.Poly := [([10,15,19], 1)]
theorem eval_atom2166 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2166 = ((g 10) * (g 15) * (g 19)) := by
  norm_num [atom2166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2166_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (141191439828480 : Int) atom2166) := by
  rw [SparsePolynomial.eval_scale, eval_atom2166]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2166Coded : CoefficientMerge.Poly := [(6139, 1)]
theorem atom2166Coded_decode : atom2166 = SparsePolynomial.decodeCubic 24 atom2166Coded := by decide +kernel
theorem atom2166Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) := by
  have h := atom2166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2167 : SparsePolynomial.Poly := [([10,15,20], 1)]
theorem eval_atom2167 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2167 = ((g 10) * (g 15) * (g 20)) := by
  norm_num [atom2167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2167_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276800336879472 : Int) atom2167) := by
  rw [SparsePolynomial.eval_scale, eval_atom2167]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2167Coded : CoefficientMerge.Poly := [(6140, 1)]
theorem atom2167Coded_decode : atom2167 = SparsePolynomial.decodeCubic 24 atom2167Coded := by decide +kernel
theorem atom2167Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) := by
  have h := atom2167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2168 : SparsePolynomial.Poly := [([10,15,21], 1)]
theorem eval_atom2168 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2168 = ((g 10) * (g 15) * (g 21)) := by
  norm_num [atom2168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2168_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323185034474280 : Int) atom2168) := by
  rw [SparsePolynomial.eval_scale, eval_atom2168]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2168Coded : CoefficientMerge.Poly := [(6141, 1)]
theorem atom2168Coded_decode : atom2168 = SparsePolynomial.decodeCubic 24 atom2168Coded := by decide +kernel
theorem atom2168Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded) := by
  have h := atom2168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2169 : SparsePolynomial.Poly := [([10,15,22], 1)]
theorem eval_atom2169 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2169 = ((g 10) * (g 15) * (g 22)) := by
  norm_num [atom2169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2169_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (355765957502688 : Int) atom2169) := by
  rw [SparsePolynomial.eval_scale, eval_atom2169]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2169Coded : CoefficientMerge.Poly := [(6142, 1)]
theorem atom2169Coded_decode : atom2169 = SparsePolynomial.decodeCubic 24 atom2169Coded := by decide +kernel
theorem atom2169Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) := by
  have h := atom2169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2170 : SparsePolynomial.Poly := [([10,15,23], 1)]
theorem eval_atom2170 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2170 = ((g 10) * (g 15) * (g 23)) := by
  norm_num [atom2170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2170_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (469518281927100 : Int) atom2170) := by
  rw [SparsePolynomial.eval_scale, eval_atom2170]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2170Coded : CoefficientMerge.Poly := [(6143, 1)]
theorem atom2170Coded_decode : atom2170 = SparsePolynomial.decodeCubic 24 atom2170Coded := by decide +kernel
theorem atom2170Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded) := by
  have h := atom2170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2171 : SparsePolynomial.Poly := [([10,16,16], 1)]
theorem eval_atom2171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2171 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom2171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87867320864400 : Int) atom2171) := by
  rw [SparsePolynomial.eval_scale, eval_atom2171]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2171Coded : CoefficientMerge.Poly := [(6160, 1)]
theorem atom2171Coded_decode : atom2171 = SparsePolynomial.decodeCubic 24 atom2171Coded := by decide +kernel
theorem atom2171Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) := by
  have h := atom2171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2172 : SparsePolynomial.Poly := [([10,16,17], 1)]
theorem eval_atom2172 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2172 = ((g 10) * (g 16) * (g 17)) := by
  norm_num [atom2172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2172_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175840953472800 : Int) atom2172) := by
  rw [SparsePolynomial.eval_scale, eval_atom2172]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2172Coded : CoefficientMerge.Poly := [(6161, 1)]
theorem atom2172Coded_decode : atom2172 = SparsePolynomial.decodeCubic 24 atom2172Coded := by decide +kernel
theorem atom2172Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) := by
  have h := atom2172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2173 : SparsePolynomial.Poly := [([10,16,18], 1)]
theorem eval_atom2173 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2173 = ((g 10) * (g 16) * (g 18)) := by
  norm_num [atom2173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2173_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176455475967888 : Int) atom2173) := by
  rw [SparsePolynomial.eval_scale, eval_atom2173]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2173Coded : CoefficientMerge.Poly := [(6162, 1)]
theorem atom2173Coded_decode : atom2173 = SparsePolynomial.decodeCubic 24 atom2173Coded := by decide +kernel
theorem atom2173Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded) := by
  have h := atom2173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2174 : SparsePolynomial.Poly := [([10,16,19], 1)]
theorem eval_atom2174 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2174 = ((g 10) * (g 16) * (g 19)) := by
  norm_num [atom2174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2174_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188873223482880 : Int) atom2174) := by
  rw [SparsePolynomial.eval_scale, eval_atom2174]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2174Coded : CoefficientMerge.Poly := [(6163, 1)]
theorem atom2174Coded_decode : atom2174 = SparsePolynomial.decodeCubic 24 atom2174Coded := by decide +kernel
theorem atom2174Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) := by
  have h := atom2174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2175 : SparsePolynomial.Poly := [([10,16,20], 1)]
theorem eval_atom2175 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2175 = ((g 10) * (g 16) * (g 20)) := by
  norm_num [atom2175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2175_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342132769449072 : Int) atom2175) := by
  rw [SparsePolynomial.eval_scale, eval_atom2175]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2175Coded : CoefficientMerge.Poly := [(6164, 1)]
theorem atom2175Coded_decode : atom2175 = SparsePolynomial.decodeCubic 24 atom2175Coded := by decide +kernel
theorem atom2175Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded) := by
  have h := atom2175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2176 : SparsePolynomial.Poly := [([10,16,21], 1)]
theorem eval_atom2176 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2176 = ((g 10) * (g 16) * (g 21)) := by
  norm_num [atom2176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2176_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402956051584680 : Int) atom2176) := by
  rw [SparsePolynomial.eval_scale, eval_atom2176]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2176Coded : CoefficientMerge.Poly := [(6165, 1)]
theorem atom2176Coded_decode : atom2176 = SparsePolynomial.decodeCubic 24 atom2176Coded := by decide +kernel
theorem atom2176Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) := by
  have h := atom2176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2177 : SparsePolynomial.Poly := [([10,16,22], 1)]
theorem eval_atom2177 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2177 = ((g 10) * (g 16) * (g 22)) := by
  norm_num [atom2177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2177_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (392182562174688 : Int) atom2177) := by
  rw [SparsePolynomial.eval_scale, eval_atom2177]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2177Coded : CoefficientMerge.Poly := [(6166, 1)]
theorem atom2177Coded_decode : atom2177 = SparsePolynomial.decodeCubic 24 atom2177Coded := by decide +kernel
theorem atom2177Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) := by
  have h := atom2177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2178 : SparsePolynomial.Poly := [([10,16,23], 1)]
theorem eval_atom2178 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2178 = ((g 10) * (g 16) * (g 23)) := by
  norm_num [atom2178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2178_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (595302229928700 : Int) atom2178) := by
  rw [SparsePolynomial.eval_scale, eval_atom2178]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2178Coded : CoefficientMerge.Poly := [(6167, 1)]
theorem atom2178Coded_decode : atom2178 = SparsePolynomial.decodeCubic 24 atom2178Coded := by decide +kernel
theorem atom2178Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded) := by
  have h := atom2178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2179 : SparsePolynomial.Poly := [([10,17,17], 1)]
theorem eval_atom2179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2179 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom2179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111950474605200 : Int) atom2179) := by
  rw [SparsePolynomial.eval_scale, eval_atom2179]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2179Coded : CoefficientMerge.Poly := [(6185, 1)]
theorem atom2179Coded_decode : atom2179 = SparsePolynomial.decodeCubic 24 atom2179Coded := by decide +kernel
theorem atom2179Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) := by
  have h := atom2179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2180 : SparsePolynomial.Poly := [([10,17,18], 1)]
theorem eval_atom2180 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2180 = ((g 10) * (g 17) * (g 18)) := by
  norm_num [atom2180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2180_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221385718393488 : Int) atom2180) := by
  rw [SparsePolynomial.eval_scale, eval_atom2180]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2180Coded : CoefficientMerge.Poly := [(6186, 1)]
theorem atom2180Coded_decode : atom2180 = SparsePolynomial.decodeCubic 24 atom2180Coded := by decide +kernel
theorem atom2180Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded) := by
  have h := atom2180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2181 : SparsePolynomial.Poly := [([10,17,19], 1)]
theorem eval_atom2181 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2181 = ((g 10) * (g 17) * (g 19)) := by
  norm_num [atom2181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2181_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256420484052480 : Int) atom2181) := by
  rw [SparsePolynomial.eval_scale, eval_atom2181]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2181Coded : CoefficientMerge.Poly := [(6187, 1)]
theorem atom2181Coded_decode : atom2181 = SparsePolynomial.decodeCubic 24 atom2181Coded := by decide +kernel
theorem atom2181Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) := by
  have h := atom2181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2182 : SparsePolynomial.Poly := [([10,17,20], 1)]
theorem eval_atom2182 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2182 = ((g 10) * (g 17) * (g 20)) := by
  norm_num [atom2182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2182_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (432297048162672 : Int) atom2182) := by
  rw [SparsePolynomial.eval_scale, eval_atom2182]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2182Coded : CoefficientMerge.Poly := [(6188, 1)]
theorem atom2182Coded_decode : atom2182 = SparsePolynomial.decodeCubic 24 atom2182Coded := by decide +kernel
theorem atom2182Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) := by
  have h := atom2182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2183 : SparsePolynomial.Poly := [([10,17,21], 1)]
theorem eval_atom2183 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2183 = ((g 10) * (g 17) * (g 21)) := by
  norm_num [atom2183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2183_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510042099453480 : Int) atom2183) := by
  rw [SparsePolynomial.eval_scale, eval_atom2183]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2183Coded : CoefficientMerge.Poly := [(6189, 1)]
theorem atom2183Coded_decode : atom2183 = SparsePolynomial.decodeCubic 24 atom2183Coded := by decide +kernel
theorem atom2183Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded) := by
  have h := atom2183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2184 : SparsePolynomial.Poly := [([10,17,22], 1)]
theorem eval_atom2184 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2184 = ((g 10) * (g 17) * (g 22)) := by
  norm_num [atom2184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2184_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (515066696280288 : Int) atom2184) := by
  rw [SparsePolynomial.eval_scale, eval_atom2184]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2184Coded : CoefficientMerge.Poly := [(6190, 1)]
theorem atom2184Coded_decode : atom2184 = SparsePolynomial.decodeCubic 24 atom2184Coded := by decide +kernel
theorem atom2184Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) := by
  have h := atom2184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2185 : SparsePolynomial.Poly := [([10,17,23], 1)]
theorem eval_atom2185 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2185 = ((g 10) * (g 17) * (g 23)) := by
  norm_num [atom2185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2185_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (732260508695100 : Int) atom2185) := by
  rw [SparsePolynomial.eval_scale, eval_atom2185]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2185Coded : CoefficientMerge.Poly := [(6191, 1)]
theorem atom2185Coded_decode : atom2185 = SparsePolynomial.decodeCubic 24 atom2185Coded := by decide +kernel
theorem atom2185Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded) := by
  have h := atom2185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2186 : SparsePolynomial.Poly := [([10,18,18], 1)]
theorem eval_atom2186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2186 = ((g 10) * (g 18) * (g 18)) := by
  norm_num [atom2186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155797451099136 : Int) atom2186) := by
  rw [SparsePolynomial.eval_scale, eval_atom2186]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2186Coded : CoefficientMerge.Poly := [(6210, 1)]
theorem atom2186Coded_decode : atom2186 = SparsePolynomial.decodeCubic 24 atom2186Coded := by decide +kernel
theorem atom2186Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) := by
  have h := atom2186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2187 : SparsePolynomial.Poly := [([10,18,19], 1)]
theorem eval_atom2187 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2187 = ((g 10) * (g 18) * (g 19)) := by
  norm_num [atom2187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2187_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337443300433008 : Int) atom2187) := by
  rw [SparsePolynomial.eval_scale, eval_atom2187]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2187Coded : CoefficientMerge.Poly := [(6211, 1)]
theorem atom2187Coded_decode : atom2187 = SparsePolynomial.decodeCubic 24 atom2187Coded := by decide +kernel
theorem atom2187Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) := by
  have h := atom2187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2188 : SparsePolynomial.Poly := [([10,18,20], 1)]
theorem eval_atom2188 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2188 = ((g 10) * (g 18) * (g 20)) := by
  norm_num [atom2188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2188_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (574554396344544 : Int) atom2188) := by
  rw [SparsePolynomial.eval_scale, eval_atom2188]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2188Coded : CoefficientMerge.Poly := [(6212, 1)]
theorem atom2188Coded_decode : atom2188 = SparsePolynomial.decodeCubic 24 atom2188Coded := by decide +kernel
theorem atom2188Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded) := by
  have h := atom2188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2189 : SparsePolynomial.Poly := [([10,18,21], 1)]
theorem eval_atom2189 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2189 = ((g 10) * (g 18) * (g 21)) := by
  norm_num [atom2189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2189_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (618751227702168 : Int) atom2189) := by
  rw [SparsePolynomial.eval_scale, eval_atom2189]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2189Coded : CoefficientMerge.Poly := [(6213, 1)]
theorem atom2189Coded_decode : atom2189 = SparsePolynomial.decodeCubic 24 atom2189Coded := by decide +kernel
theorem atom2189Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) := by
  have h := atom2189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2190 : SparsePolynomial.Poly := [([10,18,22], 1)]
theorem eval_atom2190 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2190 = ((g 10) * (g 18) * (g 22)) := by
  norm_num [atom2190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2190_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510055392621024 : Int) atom2190) := by
  rw [SparsePolynomial.eval_scale, eval_atom2190]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2190Coded : CoefficientMerge.Poly := [(6214, 1)]
theorem atom2190Coded_decode : atom2190 = SparsePolynomial.decodeCubic 24 atom2190Coded := by decide +kernel
theorem atom2190Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded) := by
  have h := atom2190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2191 : SparsePolynomial.Poly := [([10,18,23], 1)]
theorem eval_atom2191 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2191 = ((g 10) * (g 18) * (g 23)) := by
  norm_num [atom2191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2191_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (755578774750140 : Int) atom2191) := by
  rw [SparsePolynomial.eval_scale, eval_atom2191]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2191Coded : CoefficientMerge.Poly := [(6215, 1)]
theorem atom2191Coded_decode : atom2191 = SparsePolynomial.decodeCubic 24 atom2191Coded := by decide +kernel
theorem atom2191Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) := by
  have h := atom2191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2192 : SparsePolynomial.Poly := [([10,19,19], 1)]
theorem eval_atom2192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2192 = ((g 10) * (g 19) * (g 19)) := by
  norm_num [atom2192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118417314212208 : Int) atom2192) := by
  rw [SparsePolynomial.eval_scale, eval_atom2192]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2192Coded : CoefficientMerge.Poly := [(6235, 1)]
theorem atom2192Coded_decode : atom2192 = SparsePolynomial.decodeCubic 24 atom2192Coded := by decide +kernel
theorem atom2192Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) := by
  have h := atom2192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2193 : SparsePolynomial.Poly := [([10,19,20], 1)]
theorem eval_atom2193 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2193 = ((g 10) * (g 19) * (g 20)) := by
  norm_num [atom2193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2193_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457772204848464 : Int) atom2193) := by
  rw [SparsePolynomial.eval_scale, eval_atom2193]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2193Coded : CoefficientMerge.Poly := [(6236, 1)]
theorem atom2193Coded_decode : atom2193 = SparsePolynomial.decodeCubic 24 atom2193Coded := by decide +kernel
theorem atom2193Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded) := by
  have h := atom2193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2194 : SparsePolynomial.Poly := [([10,19,21], 1)]
theorem eval_atom2194 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2194 = ((g 10) * (g 19) * (g 21)) := by
  norm_num [atom2194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2194_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (509935380181128 : Int) atom2194) := by
  rw [SparsePolynomial.eval_scale, eval_atom2194]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2194Coded : CoefficientMerge.Poly := [(6237, 1)]
theorem atom2194Coded_decode : atom2194 = SparsePolynomial.decodeCubic 24 atom2194Coded := by decide +kernel
theorem atom2194Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) := by
  have h := atom2194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2195 : SparsePolynomial.Poly := [([10,19,22], 1)]
theorem eval_atom2195 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2195 = ((g 10) * (g 19) * (g 22)) := by
  norm_num [atom2195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2195_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417231228435936 : Int) atom2195) := by
  rw [SparsePolynomial.eval_scale, eval_atom2195]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2195Coded : CoefficientMerge.Poly := [(6238, 1)]
theorem atom2195Coded_decode : atom2195 = SparsePolynomial.decodeCubic 24 atom2195Coded := by decide +kernel
theorem atom2195Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded) := by
  have h := atom2195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2196 : SparsePolynomial.Poly := [([10,19,23], 1)]
theorem eval_atom2196 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2196 = ((g 10) * (g 19) * (g 23)) := by
  norm_num [atom2196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2196_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (516076854392700 : Int) atom2196) := by
  rw [SparsePolynomial.eval_scale, eval_atom2196]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2196Coded : CoefficientMerge.Poly := [(6239, 1)]
theorem atom2196Coded_decode : atom2196 = SparsePolynomial.decodeCubic 24 atom2196Coded := by decide +kernel
theorem atom2196Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) := by
  have h := atom2196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2197 : SparsePolynomial.Poly := [([10,20,20], 1)]
theorem eval_atom2197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2197 = ((g 10) * (g 20) * (g 20)) := by
  norm_num [atom2197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346547254740192 : Int) atom2197) := by
  rw [SparsePolynomial.eval_scale, eval_atom2197]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2197Coded : CoefficientMerge.Poly := [(6260, 1)]
theorem atom2197Coded_decode : atom2197 = SparsePolynomial.decodeCubic 24 atom2197Coded := by decide +kernel
theorem atom2197Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) := by
  have h := atom2197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2198 : SparsePolynomial.Poly := [([10,20,21], 1)]
theorem eval_atom2198 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2198 = ((g 10) * (g 20) * (g 21)) := by
  norm_num [atom2198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2198_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (577171780724088 : Int) atom2198) := by
  rw [SparsePolynomial.eval_scale, eval_atom2198]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2198Coded : CoefficientMerge.Poly := [(6261, 1)]
theorem atom2198Coded_decode : atom2198 = SparsePolynomial.decodeCubic 24 atom2198Coded := by decide +kernel
theorem atom2198Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded) := by
  have h := atom2198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2199 : SparsePolynomial.Poly := [([10,20,22], 1)]
theorem eval_atom2199 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2199 = ((g 10) * (g 20) * (g 22)) := by
  norm_num [atom2199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2199_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (437315251001568 : Int) atom2199) := by
  rw [SparsePolynomial.eval_scale, eval_atom2199]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2199Coded : CoefficientMerge.Poly := [(6262, 1)]
theorem atom2199Coded_decode : atom2199 = SparsePolynomial.decodeCubic 24 atom2199Coded := by decide +kernel
theorem atom2199Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) := by
  have h := atom2199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2200 : SparsePolynomial.Poly := [([10,20,23], 1)]
theorem eval_atom2200 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2200 = ((g 10) * (g 20) * (g 23)) := by
  norm_num [atom2200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2200_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (473142522455676 : Int) atom2200) := by
  rw [SparsePolynomial.eval_scale, eval_atom2200]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2200Coded : CoefficientMerge.Poly := [(6263, 1)]
theorem atom2200Coded_decode : atom2200 = SparsePolynomial.decodeCubic 24 atom2200Coded := by decide +kernel
theorem atom2200Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded) := by
  have h := atom2200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2201 : SparsePolynomial.Poly := [([10,21,21], 1)]
theorem eval_atom2201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2201 = ((g 10) * (g 21) * (g 21)) := by
  norm_num [atom2201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169648736717592 : Int) atom2201) := by
  rw [SparsePolynomial.eval_scale, eval_atom2201]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2201Coded : CoefficientMerge.Poly := [(6285, 1)]
theorem atom2201Coded_decode : atom2201 = SparsePolynomial.decodeCubic 24 atom2201Coded := by decide +kernel
theorem atom2201Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) := by
  have h := atom2201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2202 : SparsePolynomial.Poly := [([10,21,22], 1)]
theorem eval_atom2202 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2202 = ((g 10) * (g 21) * (g 22)) := by
  norm_num [atom2202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2202_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230976346924512 : Int) atom2202) := by
  rw [SparsePolynomial.eval_scale, eval_atom2202]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2202Coded : CoefficientMerge.Poly := [(6286, 1)]
theorem atom2202Coded_decode : atom2202 = SparsePolynomial.decodeCubic 24 atom2202Coded := by decide +kernel
theorem atom2202Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) := by
  have h := atom2202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2203 : SparsePolynomial.Poly := [([10,21,23], 1)]
theorem eval_atom2203 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2203 = ((g 10) * (g 21) * (g 23)) := by
  norm_num [atom2203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2203_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (260856825525180 : Int) atom2203) := by
  rw [SparsePolynomial.eval_scale, eval_atom2203]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 10) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2203Coded : CoefficientMerge.Poly := [(6287, 1)]
theorem atom2203Coded_decode : atom2203 = SparsePolynomial.decodeCubic 24 atom2203Coded := by decide +kernel
theorem atom2203Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded) := by
  have h := atom2203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2204 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom2204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2204 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom2204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10703377792800 : Int) atom2204) := by
  rw [SparsePolynomial.eval_scale, eval_atom2204]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2204Coded : CoefficientMerge.Poly := [(6611, 1)]
theorem atom2204Coded_decode : atom2204 = SparsePolynomial.decodeCubic 24 atom2204Coded := by decide +kernel
theorem atom2204Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) := by
  have h := atom2204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2205 : SparsePolynomial.Poly := [([11,11,12], 1)]
theorem eval_atom2205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2205 = ((g 11) * (g 11) * (g 12)) := by
  norm_num [atom2205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom2205) := by
  rw [SparsePolynomial.eval_scale, eval_atom2205]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2205Coded : CoefficientMerge.Poly := [(6612, 1)]
theorem atom2205Coded_decode : atom2205 = SparsePolynomial.decodeCubic 24 atom2205Coded := by decide +kernel
theorem atom2205Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded) := by
  have h := atom2205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2206 : SparsePolynomial.Poly := [([11,11,13], 1)]
theorem eval_atom2206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2206 = ((g 11) * (g 11) * (g 13)) := by
  norm_num [atom2206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2206) := by
  rw [SparsePolynomial.eval_scale, eval_atom2206]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2206Coded : CoefficientMerge.Poly := [(6613, 1)]
theorem atom2206Coded_decode : atom2206 = SparsePolynomial.decodeCubic 24 atom2206Coded := by decide +kernel
theorem atom2206Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) := by
  have h := atom2206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2207 : SparsePolynomial.Poly := [([11,11,14], 1)]
theorem eval_atom2207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2207 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom2207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2207) := by
  rw [SparsePolynomial.eval_scale, eval_atom2207]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2207Coded : CoefficientMerge.Poly := [(6614, 1)]
theorem atom2207Coded_decode : atom2207 = SparsePolynomial.decodeCubic 24 atom2207Coded := by decide +kernel
theorem atom2207Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) := by
  have h := atom2207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2208 : SparsePolynomial.Poly := [([11,11,18], 1)]
theorem eval_atom2208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2208 = ((g 11) * (g 11) * (g 18)) := by
  norm_num [atom2208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11628748118592 : Int) atom2208) := by
  rw [SparsePolynomial.eval_scale, eval_atom2208]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2208Coded : CoefficientMerge.Poly := [(6618, 1)]
theorem atom2208Coded_decode : atom2208 = SparsePolynomial.decodeCubic 24 atom2208Coded := by decide +kernel
theorem atom2208Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded) := by
  have h := atom2208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block029 : CoefficientMerge.Poly := [(6047, 144759386217600), (6060, 11171370949200), (6061, 15674337756000), (6062, 20819826165600), (6063, 25965314575200), (6064, 31110802984800), (6065, 36256291394400), (6066, 45334222105392), (6068, 62475180994512), (6069, 74122873486200), (6070, 153208246292640), (6071, 247986262408500), (6085, 27104843581200), (6086, 48070183946400), (6087, 51174486871200), (6088, 57361830372000), (6089, 63549173872800), (6090, 73075050903888), (6091, 42531469390080), (6092, 123990436996272), (6093, 139283462035080), (6094, 231954760353888), (6095, 339742267533900), (6110, 43567217139600), (6111, 85125142317600), (6112, 91333748167200), (6113, 97542354016800), (6114, 98659441119888), (6115, 89005622222880), (6116, 181911628693872), (6117, 210902114186280), (6118, 296892084189888), (6119, 409342572985500), (6135, 67242842528400), (6136, 126342205466400), (6137, 131551480922400), (6138, 146424341228688), (6139, 141191439828480), (6140, 276800336879472), (6141, 323185034474280), (6142, 355765957502688), (6143, 469518281927100), (6160, 87867320864400), (6161, 175840953472800), (6162, 176455475967888), (6163, 188873223482880), (6164, 342132769449072), (6165, 402956051584680), (6166, 392182562174688), (6167, 595302229928700), (6185, 111950474605200), (6186, 221385718393488), (6187, 256420484052480), (6188, 432297048162672), (6189, 510042099453480), (6190, 515066696280288), (6191, 732260508695100), (6210, 155797451099136), (6211, 337443300433008), (6212, 574554396344544), (6213, 618751227702168), (6214, 510055392621024), (6215, 755578774750140), (6235, 118417314212208), (6236, 457772204848464), (6237, 509935380181128), (6238, 417231228435936), (6239, 516076854392700), (6260, 346547254740192), (6261, 577171780724088), (6262, 437315251001568), (6263, 473142522455676), (6285, 169648736717592), (6286, 230976346924512), (6287, 260856825525180), (6611, 10703377792800), (6612, 9249121728000), (6613, 6166081152000), (6614, 3083040576000), (6618, 11628748118592)]
theorem block029_data : block029 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)))))))) := by decide +kernel
theorem block029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block029 := by
  rw [block029_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2129Coded_nonneg g hg hA hB) (atom2130Coded_nonneg g hg hA hB)) (add_nonneg (atom2131Coded_nonneg g hg hA hB) (add_nonneg (atom2132Coded_nonneg g hg hA hB) (atom2133Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2134Coded_nonneg g hg hA hB) (atom2135Coded_nonneg g hg hA hB)) (add_nonneg (atom2136Coded_nonneg g hg hA hB) (add_nonneg (atom2137Coded_nonneg g hg hA hB) (atom2138Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2139Coded_nonneg g hg hA hB) (atom2140Coded_nonneg g hg hA hB)) (add_nonneg (atom2141Coded_nonneg g hg hA hB) (add_nonneg (atom2142Coded_nonneg g hg hA hB) (atom2143Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2144Coded_nonneg g hg hA hB) (atom2145Coded_nonneg g hg hA hB)) (add_nonneg (atom2146Coded_nonneg g hg hA hB) (add_nonneg (atom2147Coded_nonneg g hg hA hB) (atom2148Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2149Coded_nonneg g hg hA hB) (atom2150Coded_nonneg g hg hA hB)) (add_nonneg (atom2151Coded_nonneg g hg hA hB) (add_nonneg (atom2152Coded_nonneg g hg hA hB) (atom2153Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2154Coded_nonneg g hg hA hB) (atom2155Coded_nonneg g hg hA hB)) (add_nonneg (atom2156Coded_nonneg g hg hA hB) (add_nonneg (atom2157Coded_nonneg g hg hA hB) (atom2158Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2159Coded_nonneg g hg hA hB) (atom2160Coded_nonneg g hg hA hB)) (add_nonneg (atom2161Coded_nonneg g hg hA hB) (add_nonneg (atom2162Coded_nonneg g hg hA hB) (atom2163Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2164Coded_nonneg g hg hA hB) (atom2165Coded_nonneg g hg hA hB)) (add_nonneg (atom2166Coded_nonneg g hg hA hB) (add_nonneg (atom2167Coded_nonneg g hg hA hB) (atom2168Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2169Coded_nonneg g hg hA hB) (atom2170Coded_nonneg g hg hA hB)) (add_nonneg (atom2171Coded_nonneg g hg hA hB) (add_nonneg (atom2172Coded_nonneg g hg hA hB) (atom2173Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2174Coded_nonneg g hg hA hB) (atom2175Coded_nonneg g hg hA hB)) (add_nonneg (atom2176Coded_nonneg g hg hA hB) (add_nonneg (atom2177Coded_nonneg g hg hA hB) (atom2178Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2179Coded_nonneg g hg hA hB) (atom2180Coded_nonneg g hg hA hB)) (add_nonneg (atom2181Coded_nonneg g hg hA hB) (add_nonneg (atom2182Coded_nonneg g hg hA hB) (atom2183Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2184Coded_nonneg g hg hA hB) (atom2185Coded_nonneg g hg hA hB)) (add_nonneg (atom2186Coded_nonneg g hg hA hB) (add_nonneg (atom2187Coded_nonneg g hg hA hB) (atom2188Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2189Coded_nonneg g hg hA hB) (atom2190Coded_nonneg g hg hA hB)) (add_nonneg (atom2191Coded_nonneg g hg hA hB) (add_nonneg (atom2192Coded_nonneg g hg hA hB) (atom2193Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2194Coded_nonneg g hg hA hB) (atom2195Coded_nonneg g hg hA hB)) (add_nonneg (atom2196Coded_nonneg g hg hA hB) (add_nonneg (atom2197Coded_nonneg g hg hA hB) (atom2198Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2199Coded_nonneg g hg hA hB) (atom2200Coded_nonneg g hg hA hB)) (add_nonneg (atom2201Coded_nonneg g hg hA hB) (add_nonneg (atom2202Coded_nonneg g hg hA hB) (atom2203Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2204Coded_nonneg g hg hA hB) (atom2205Coded_nonneg g hg hA hB)) (add_nonneg (atom2206Coded_nonneg g hg hA hB) (add_nonneg (atom2207Coded_nonneg g hg hA hB) (atom2208Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
