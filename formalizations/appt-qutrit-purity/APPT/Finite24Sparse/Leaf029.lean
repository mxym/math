-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2129 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2129Coded : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 1))]
theorem atom2129Coded_decode : atom2129 = SparsePolynomial.decodeCubic 24 atom2129Coded := by decide +kernel
theorem atom2129Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) := by
  have h := atom2129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2130 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom2130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2130 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom2130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171370949200 : Int) atom2130) := by
  rw [SparsePolynomial.eval_scale, eval_atom2130]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2130Coded : CoefficientMerge.Poly := [(nat_lit 6060, Int.ofNat (nat_lit 1))]
theorem atom2130Coded_decode : atom2130 = SparsePolynomial.decodeCubic 24 atom2130Coded := by decide +kernel
theorem atom2130Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded) := by
  have h := atom2130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2131 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom2131Coded : CoefficientMerge.Poly := [(nat_lit 6061, Int.ofNat (nat_lit 1))]
theorem atom2131Coded_decode : atom2131 = SparsePolynomial.decodeCubic 24 atom2131Coded := by decide +kernel
theorem atom2131Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) := by
  have h := atom2131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2132 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom2132Coded : CoefficientMerge.Poly := [(nat_lit 6062, Int.ofNat (nat_lit 1))]
theorem atom2132Coded_decode : atom2132 = SparsePolynomial.decodeCubic 24 atom2132Coded := by decide +kernel
theorem atom2132Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) := by
  have h := atom2132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2133 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom2133Coded : CoefficientMerge.Poly := [(nat_lit 6063, Int.ofNat (nat_lit 1))]
theorem atom2133Coded_decode : atom2133 = SparsePolynomial.decodeCubic 24 atom2133Coded := by decide +kernel
theorem atom2133Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded) := by
  have h := atom2133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2134 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom2134Coded : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 1))]
theorem atom2134Coded_decode : atom2134 = SparsePolynomial.decodeCubic 24 atom2134Coded := by decide +kernel
theorem atom2134Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) := by
  have h := atom2134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2135 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom2135Coded : CoefficientMerge.Poly := [(nat_lit 6065, Int.ofNat (nat_lit 1))]
theorem atom2135Coded_decode : atom2135 = SparsePolynomial.decodeCubic 24 atom2135Coded := by decide +kernel
theorem atom2135Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded) := by
  have h := atom2135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2136 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2136Coded : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 1))]
theorem atom2136Coded_decode : atom2136 = SparsePolynomial.decodeCubic 24 atom2136Coded := by decide +kernel
theorem atom2136Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) := by
  have h := atom2136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2137 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2137Coded : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 1))]
theorem atom2137Coded_decode : atom2137 = SparsePolynomial.decodeCubic 24 atom2137Coded := by decide +kernel
theorem atom2137Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) := by
  have h := atom2137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2138 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2138Coded : CoefficientMerge.Poly := [(nat_lit 6069, Int.ofNat (nat_lit 1))]
theorem atom2138Coded_decode : atom2138 = SparsePolynomial.decodeCubic 24 atom2138Coded := by decide +kernel
theorem atom2138Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded) := by
  have h := atom2138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2139 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2139Coded : CoefficientMerge.Poly := [(nat_lit 6070, Int.ofNat (nat_lit 1))]
theorem atom2139Coded_decode : atom2139 = SparsePolynomial.decodeCubic 24 atom2139Coded := by decide +kernel
theorem atom2139Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) := by
  have h := atom2139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2140 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2140Coded : CoefficientMerge.Poly := [(nat_lit 6071, Int.ofNat (nat_lit 1))]
theorem atom2140Coded_decode : atom2140 = SparsePolynomial.decodeCubic 24 atom2140Coded := by decide +kernel
theorem atom2140Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded) := by
  have h := atom2140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2141 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2141 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom2141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27104843581200 : Int) atom2141) := by
  rw [SparsePolynomial.eval_scale, eval_atom2141]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2141Coded : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 1))]
theorem atom2141Coded_decode : atom2141 = SparsePolynomial.decodeCubic 24 atom2141Coded := by decide +kernel
theorem atom2141Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) := by
  have h := atom2141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2142 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom2142Coded : CoefficientMerge.Poly := [(nat_lit 6086, Int.ofNat (nat_lit 1))]
theorem atom2142Coded_decode : atom2142 = SparsePolynomial.decodeCubic 24 atom2142Coded := by decide +kernel
theorem atom2142Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) := by
  have h := atom2142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2143 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom2143Coded : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 1))]
theorem atom2143Coded_decode : atom2143 = SparsePolynomial.decodeCubic 24 atom2143Coded := by decide +kernel
theorem atom2143Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded) := by
  have h := atom2143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2144 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom2144Coded : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 1))]
theorem atom2144Coded_decode : atom2144 = SparsePolynomial.decodeCubic 24 atom2144Coded := by decide +kernel
theorem atom2144Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) := by
  have h := atom2144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2145 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom2145Coded : CoefficientMerge.Poly := [(nat_lit 6089, Int.ofNat (nat_lit 1))]
theorem atom2145Coded_decode : atom2145 = SparsePolynomial.decodeCubic 24 atom2145Coded := by decide +kernel
theorem atom2145Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded) := by
  have h := atom2145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2146 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2146Coded : CoefficientMerge.Poly := [(nat_lit 6090, Int.ofNat (nat_lit 1))]
theorem atom2146Coded_decode : atom2146 = SparsePolynomial.decodeCubic 24 atom2146Coded := by decide +kernel
theorem atom2146Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) := by
  have h := atom2146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2147 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2147Coded : CoefficientMerge.Poly := [(nat_lit 6091, Int.ofNat (nat_lit 1))]
theorem atom2147Coded_decode : atom2147 = SparsePolynomial.decodeCubic 24 atom2147Coded := by decide +kernel
theorem atom2147Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) := by
  have h := atom2147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2148 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2148Coded : CoefficientMerge.Poly := [(nat_lit 6092, Int.ofNat (nat_lit 1))]
theorem atom2148Coded_decode : atom2148 = SparsePolynomial.decodeCubic 24 atom2148Coded := by decide +kernel
theorem atom2148Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded) := by
  have h := atom2148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2149 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2149Coded : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 1))]
theorem atom2149Coded_decode : atom2149 = SparsePolynomial.decodeCubic 24 atom2149Coded := by decide +kernel
theorem atom2149Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) := by
  have h := atom2149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2150 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2150Coded : CoefficientMerge.Poly := [(nat_lit 6094, Int.ofNat (nat_lit 1))]
theorem atom2150Coded_decode : atom2150 = SparsePolynomial.decodeCubic 24 atom2150Coded := by decide +kernel
theorem atom2150Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded) := by
  have h := atom2150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2151 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2151Coded : CoefficientMerge.Poly := [(nat_lit 6095, Int.ofNat (nat_lit 1))]
theorem atom2151Coded_decode : atom2151 = SparsePolynomial.decodeCubic 24 atom2151Coded := by decide +kernel
theorem atom2151Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) := by
  have h := atom2151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2152 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2152 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom2152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43567217139600 : Int) atom2152) := by
  rw [SparsePolynomial.eval_scale, eval_atom2152]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2152Coded : CoefficientMerge.Poly := [(nat_lit 6110, Int.ofNat (nat_lit 1))]
theorem atom2152Coded_decode : atom2152 = SparsePolynomial.decodeCubic 24 atom2152Coded := by decide +kernel
theorem atom2152Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) := by
  have h := atom2152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2153 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom2153Coded : CoefficientMerge.Poly := [(nat_lit 6111, Int.ofNat (nat_lit 1))]
theorem atom2153Coded_decode : atom2153 = SparsePolynomial.decodeCubic 24 atom2153Coded := by decide +kernel
theorem atom2153Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded) := by
  have h := atom2153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2154 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom2154Coded : CoefficientMerge.Poly := [(nat_lit 6112, Int.ofNat (nat_lit 1))]
theorem atom2154Coded_decode : atom2154 = SparsePolynomial.decodeCubic 24 atom2154Coded := by decide +kernel
theorem atom2154Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) := by
  have h := atom2154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2155 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom2155Coded : CoefficientMerge.Poly := [(nat_lit 6113, Int.ofNat (nat_lit 1))]
theorem atom2155Coded_decode : atom2155 = SparsePolynomial.decodeCubic 24 atom2155Coded := by decide +kernel
theorem atom2155Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded) := by
  have h := atom2155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2156 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2156Coded : CoefficientMerge.Poly := [(nat_lit 6114, Int.ofNat (nat_lit 1))]
theorem atom2156Coded_decode : atom2156 = SparsePolynomial.decodeCubic 24 atom2156Coded := by decide +kernel
theorem atom2156Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) := by
  have h := atom2156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2157 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2157Coded : CoefficientMerge.Poly := [(nat_lit 6115, Int.ofNat (nat_lit 1))]
theorem atom2157Coded_decode : atom2157 = SparsePolynomial.decodeCubic 24 atom2157Coded := by decide +kernel
theorem atom2157Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) := by
  have h := atom2157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2158 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2158Coded : CoefficientMerge.Poly := [(nat_lit 6116, Int.ofNat (nat_lit 1))]
theorem atom2158Coded_decode : atom2158 = SparsePolynomial.decodeCubic 24 atom2158Coded := by decide +kernel
theorem atom2158Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded) := by
  have h := atom2158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2159 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2159Coded : CoefficientMerge.Poly := [(nat_lit 6117, Int.ofNat (nat_lit 1))]
theorem atom2159Coded_decode : atom2159 = SparsePolynomial.decodeCubic 24 atom2159Coded := by decide +kernel
theorem atom2159Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) := by
  have h := atom2159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2160 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2160Coded : CoefficientMerge.Poly := [(nat_lit 6118, Int.ofNat (nat_lit 1))]
theorem atom2160Coded_decode : atom2160 = SparsePolynomial.decodeCubic 24 atom2160Coded := by decide +kernel
theorem atom2160Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded) := by
  have h := atom2160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2161 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2161Coded : CoefficientMerge.Poly := [(nat_lit 6119, Int.ofNat (nat_lit 1))]
theorem atom2161Coded_decode : atom2161 = SparsePolynomial.decodeCubic 24 atom2161Coded := by decide +kernel
theorem atom2161Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) := by
  have h := atom2161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2162 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2162 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom2162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67242842528400 : Int) atom2162) := by
  rw [SparsePolynomial.eval_scale, eval_atom2162]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2162Coded : CoefficientMerge.Poly := [(nat_lit 6135, Int.ofNat (nat_lit 1))]
theorem atom2162Coded_decode : atom2162 = SparsePolynomial.decodeCubic 24 atom2162Coded := by decide +kernel
theorem atom2162Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) := by
  have h := atom2162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2163 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom2163Coded : CoefficientMerge.Poly := [(nat_lit 6136, Int.ofNat (nat_lit 1))]
theorem atom2163Coded_decode : atom2163 = SparsePolynomial.decodeCubic 24 atom2163Coded := by decide +kernel
theorem atom2163Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded) := by
  have h := atom2163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2164 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom2164Coded : CoefficientMerge.Poly := [(nat_lit 6137, Int.ofNat (nat_lit 1))]
theorem atom2164Coded_decode : atom2164 = SparsePolynomial.decodeCubic 24 atom2164Coded := by decide +kernel
theorem atom2164Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) := by
  have h := atom2164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2165 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2165Coded : CoefficientMerge.Poly := [(nat_lit 6138, Int.ofNat (nat_lit 1))]
theorem atom2165Coded_decode : atom2165 = SparsePolynomial.decodeCubic 24 atom2165Coded := by decide +kernel
theorem atom2165Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded) := by
  have h := atom2165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2166 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2166Coded : CoefficientMerge.Poly := [(nat_lit 6139, Int.ofNat (nat_lit 1))]
theorem atom2166Coded_decode : atom2166 = SparsePolynomial.decodeCubic 24 atom2166Coded := by decide +kernel
theorem atom2166Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) := by
  have h := atom2166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2167 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2167Coded : CoefficientMerge.Poly := [(nat_lit 6140, Int.ofNat (nat_lit 1))]
theorem atom2167Coded_decode : atom2167 = SparsePolynomial.decodeCubic 24 atom2167Coded := by decide +kernel
theorem atom2167Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) := by
  have h := atom2167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2168 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2168Coded : CoefficientMerge.Poly := [(nat_lit 6141, Int.ofNat (nat_lit 1))]
theorem atom2168Coded_decode : atom2168 = SparsePolynomial.decodeCubic 24 atom2168Coded := by decide +kernel
theorem atom2168Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded) := by
  have h := atom2168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2169 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2169Coded : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 1))]
theorem atom2169Coded_decode : atom2169 = SparsePolynomial.decodeCubic 24 atom2169Coded := by decide +kernel
theorem atom2169Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) := by
  have h := atom2169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2170 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2170Coded : CoefficientMerge.Poly := [(nat_lit 6143, Int.ofNat (nat_lit 1))]
theorem atom2170Coded_decode : atom2170 = SparsePolynomial.decodeCubic 24 atom2170Coded := by decide +kernel
theorem atom2170Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded) := by
  have h := atom2170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2171 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2171 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom2171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87867320864400 : Int) atom2171) := by
  rw [SparsePolynomial.eval_scale, eval_atom2171]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2171Coded : CoefficientMerge.Poly := [(nat_lit 6160, Int.ofNat (nat_lit 1))]
theorem atom2171Coded_decode : atom2171 = SparsePolynomial.decodeCubic 24 atom2171Coded := by decide +kernel
theorem atom2171Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) := by
  have h := atom2171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2172 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom2172Coded : CoefficientMerge.Poly := [(nat_lit 6161, Int.ofNat (nat_lit 1))]
theorem atom2172Coded_decode : atom2172 = SparsePolynomial.decodeCubic 24 atom2172Coded := by decide +kernel
theorem atom2172Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) := by
  have h := atom2172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2173 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2173Coded : CoefficientMerge.Poly := [(nat_lit 6162, Int.ofNat (nat_lit 1))]
theorem atom2173Coded_decode : atom2173 = SparsePolynomial.decodeCubic 24 atom2173Coded := by decide +kernel
theorem atom2173Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded) := by
  have h := atom2173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2174 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2174Coded : CoefficientMerge.Poly := [(nat_lit 6163, Int.ofNat (nat_lit 1))]
theorem atom2174Coded_decode : atom2174 = SparsePolynomial.decodeCubic 24 atom2174Coded := by decide +kernel
theorem atom2174Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) := by
  have h := atom2174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2175 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2175Coded : CoefficientMerge.Poly := [(nat_lit 6164, Int.ofNat (nat_lit 1))]
theorem atom2175Coded_decode : atom2175 = SparsePolynomial.decodeCubic 24 atom2175Coded := by decide +kernel
theorem atom2175Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded) := by
  have h := atom2175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2176 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2176Coded : CoefficientMerge.Poly := [(nat_lit 6165, Int.ofNat (nat_lit 1))]
theorem atom2176Coded_decode : atom2176 = SparsePolynomial.decodeCubic 24 atom2176Coded := by decide +kernel
theorem atom2176Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) := by
  have h := atom2176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2177 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2177Coded : CoefficientMerge.Poly := [(nat_lit 6166, Int.ofNat (nat_lit 1))]
theorem atom2177Coded_decode : atom2177 = SparsePolynomial.decodeCubic 24 atom2177Coded := by decide +kernel
theorem atom2177Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) := by
  have h := atom2177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2178 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2178Coded : CoefficientMerge.Poly := [(nat_lit 6167, Int.ofNat (nat_lit 1))]
theorem atom2178Coded_decode : atom2178 = SparsePolynomial.decodeCubic 24 atom2178Coded := by decide +kernel
theorem atom2178Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded) := by
  have h := atom2178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2179 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2179 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom2179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111950474605200 : Int) atom2179) := by
  rw [SparsePolynomial.eval_scale, eval_atom2179]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2179Coded : CoefficientMerge.Poly := [(nat_lit 6185, Int.ofNat (nat_lit 1))]
theorem atom2179Coded_decode : atom2179 = SparsePolynomial.decodeCubic 24 atom2179Coded := by decide +kernel
theorem atom2179Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) := by
  have h := atom2179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2180 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom2180Coded : CoefficientMerge.Poly := [(nat_lit 6186, Int.ofNat (nat_lit 1))]
theorem atom2180Coded_decode : atom2180 = SparsePolynomial.decodeCubic 24 atom2180Coded := by decide +kernel
theorem atom2180Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded) := by
  have h := atom2180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2181 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2181Coded : CoefficientMerge.Poly := [(nat_lit 6187, Int.ofNat (nat_lit 1))]
theorem atom2181Coded_decode : atom2181 = SparsePolynomial.decodeCubic 24 atom2181Coded := by decide +kernel
theorem atom2181Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) := by
  have h := atom2181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2182 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2182Coded : CoefficientMerge.Poly := [(nat_lit 6188, Int.ofNat (nat_lit 1))]
theorem atom2182Coded_decode : atom2182 = SparsePolynomial.decodeCubic 24 atom2182Coded := by decide +kernel
theorem atom2182Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) := by
  have h := atom2182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2183 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2183Coded : CoefficientMerge.Poly := [(nat_lit 6189, Int.ofNat (nat_lit 1))]
theorem atom2183Coded_decode : atom2183 = SparsePolynomial.decodeCubic 24 atom2183Coded := by decide +kernel
theorem atom2183Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded) := by
  have h := atom2183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2184 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2184Coded : CoefficientMerge.Poly := [(nat_lit 6190, Int.ofNat (nat_lit 1))]
theorem atom2184Coded_decode : atom2184 = SparsePolynomial.decodeCubic 24 atom2184Coded := by decide +kernel
theorem atom2184Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) := by
  have h := atom2184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2185 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2185Coded : CoefficientMerge.Poly := [(nat_lit 6191, Int.ofNat (nat_lit 1))]
theorem atom2185Coded_decode : atom2185 = SparsePolynomial.decodeCubic 24 atom2185Coded := by decide +kernel
theorem atom2185Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded) := by
  have h := atom2185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2186 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2186 = ((g 10) * (g 18) * (g 18)) := by
  norm_num [atom2186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155797451099136 : Int) atom2186) := by
  rw [SparsePolynomial.eval_scale, eval_atom2186]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2186Coded : CoefficientMerge.Poly := [(nat_lit 6210, Int.ofNat (nat_lit 1))]
theorem atom2186Coded_decode : atom2186 = SparsePolynomial.decodeCubic 24 atom2186Coded := by decide +kernel
theorem atom2186Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) := by
  have h := atom2186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2187 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom2187Coded : CoefficientMerge.Poly := [(nat_lit 6211, Int.ofNat (nat_lit 1))]
theorem atom2187Coded_decode : atom2187 = SparsePolynomial.decodeCubic 24 atom2187Coded := by decide +kernel
theorem atom2187Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) := by
  have h := atom2187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2188 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2188Coded : CoefficientMerge.Poly := [(nat_lit 6212, Int.ofNat (nat_lit 1))]
theorem atom2188Coded_decode : atom2188 = SparsePolynomial.decodeCubic 24 atom2188Coded := by decide +kernel
theorem atom2188Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded) := by
  have h := atom2188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2189 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2189Coded : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 1))]
theorem atom2189Coded_decode : atom2189 = SparsePolynomial.decodeCubic 24 atom2189Coded := by decide +kernel
theorem atom2189Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) := by
  have h := atom2189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2190 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2190Coded : CoefficientMerge.Poly := [(nat_lit 6214, Int.ofNat (nat_lit 1))]
theorem atom2190Coded_decode : atom2190 = SparsePolynomial.decodeCubic 24 atom2190Coded := by decide +kernel
theorem atom2190Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded) := by
  have h := atom2190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2191 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2191Coded : CoefficientMerge.Poly := [(nat_lit 6215, Int.ofNat (nat_lit 1))]
theorem atom2191Coded_decode : atom2191 = SparsePolynomial.decodeCubic 24 atom2191Coded := by decide +kernel
theorem atom2191Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) := by
  have h := atom2191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2192 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2192 = ((g 10) * (g 19) * (g 19)) := by
  norm_num [atom2192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118417314212208 : Int) atom2192) := by
  rw [SparsePolynomial.eval_scale, eval_atom2192]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2192Coded : CoefficientMerge.Poly := [(nat_lit 6235, Int.ofNat (nat_lit 1))]
theorem atom2192Coded_decode : atom2192 = SparsePolynomial.decodeCubic 24 atom2192Coded := by decide +kernel
theorem atom2192Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) := by
  have h := atom2192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2193 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom2193Coded : CoefficientMerge.Poly := [(nat_lit 6236, Int.ofNat (nat_lit 1))]
theorem atom2193Coded_decode : atom2193 = SparsePolynomial.decodeCubic 24 atom2193Coded := by decide +kernel
theorem atom2193Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded) := by
  have h := atom2193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2194 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2194Coded : CoefficientMerge.Poly := [(nat_lit 6237, Int.ofNat (nat_lit 1))]
theorem atom2194Coded_decode : atom2194 = SparsePolynomial.decodeCubic 24 atom2194Coded := by decide +kernel
theorem atom2194Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) := by
  have h := atom2194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2195 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2195Coded : CoefficientMerge.Poly := [(nat_lit 6238, Int.ofNat (nat_lit 1))]
theorem atom2195Coded_decode : atom2195 = SparsePolynomial.decodeCubic 24 atom2195Coded := by decide +kernel
theorem atom2195Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded) := by
  have h := atom2195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2196 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2196Coded : CoefficientMerge.Poly := [(nat_lit 6239, Int.ofNat (nat_lit 1))]
theorem atom2196Coded_decode : atom2196 = SparsePolynomial.decodeCubic 24 atom2196Coded := by decide +kernel
theorem atom2196Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) := by
  have h := atom2196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2197 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2197 = ((g 10) * (g 20) * (g 20)) := by
  norm_num [atom2197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346547254740192 : Int) atom2197) := by
  rw [SparsePolynomial.eval_scale, eval_atom2197]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2197Coded : CoefficientMerge.Poly := [(nat_lit 6260, Int.ofNat (nat_lit 1))]
theorem atom2197Coded_decode : atom2197 = SparsePolynomial.decodeCubic 24 atom2197Coded := by decide +kernel
theorem atom2197Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) := by
  have h := atom2197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2198 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
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
def atom2198Coded : CoefficientMerge.Poly := [(nat_lit 6261, Int.ofNat (nat_lit 1))]
theorem atom2198Coded_decode : atom2198 = SparsePolynomial.decodeCubic 24 atom2198Coded := by decide +kernel
theorem atom2198Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded) := by
  have h := atom2198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2199 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2199Coded : CoefficientMerge.Poly := [(nat_lit 6262, Int.ofNat (nat_lit 1))]
theorem atom2199Coded_decode : atom2199 = SparsePolynomial.decodeCubic 24 atom2199Coded := by decide +kernel
theorem atom2199Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) := by
  have h := atom2199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2200 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2200Coded : CoefficientMerge.Poly := [(nat_lit 6263, Int.ofNat (nat_lit 1))]
theorem atom2200Coded_decode : atom2200 = SparsePolynomial.decodeCubic 24 atom2200Coded := by decide +kernel
theorem atom2200Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded) := by
  have h := atom2200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2201 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2201 = ((g 10) * (g 21) * (g 21)) := by
  norm_num [atom2201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169648736717592 : Int) atom2201) := by
  rw [SparsePolynomial.eval_scale, eval_atom2201]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2201Coded : CoefficientMerge.Poly := [(nat_lit 6285, Int.ofNat (nat_lit 1))]
theorem atom2201Coded_decode : atom2201 = SparsePolynomial.decodeCubic 24 atom2201Coded := by decide +kernel
theorem atom2201Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) := by
  have h := atom2201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2202 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
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
def atom2202Coded : CoefficientMerge.Poly := [(nat_lit 6286, Int.ofNat (nat_lit 1))]
theorem atom2202Coded_decode : atom2202 = SparsePolynomial.decodeCubic 24 atom2202Coded := by decide +kernel
theorem atom2202Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) := by
  have h := atom2202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2203 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
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
def atom2203Coded : CoefficientMerge.Poly := [(nat_lit 6287, Int.ofNat (nat_lit 1))]
theorem atom2203Coded_decode : atom2203 = SparsePolynomial.decodeCubic 24 atom2203Coded := by decide +kernel
theorem atom2203Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded) := by
  have h := atom2203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2204 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom2204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2204 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom2204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10703377792800 : Int) atom2204) := by
  rw [SparsePolynomial.eval_scale, eval_atom2204]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2204Coded : CoefficientMerge.Poly := [(nat_lit 6611, Int.ofNat (nat_lit 1))]
theorem atom2204Coded_decode : atom2204 = SparsePolynomial.decodeCubic 24 atom2204Coded := by decide +kernel
theorem atom2204Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) := by
  have h := atom2204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2205 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom2205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2205 = ((g 11) * (g 11) * (g 12)) := by
  norm_num [atom2205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom2205) := by
  rw [SparsePolynomial.eval_scale, eval_atom2205]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2205Coded : CoefficientMerge.Poly := [(nat_lit 6612, Int.ofNat (nat_lit 1))]
theorem atom2205Coded_decode : atom2205 = SparsePolynomial.decodeCubic 24 atom2205Coded := by decide +kernel
theorem atom2205Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded) := by
  have h := atom2205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2206 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2206 = ((g 11) * (g 11) * (g 13)) := by
  norm_num [atom2206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2206) := by
  rw [SparsePolynomial.eval_scale, eval_atom2206]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2206Coded : CoefficientMerge.Poly := [(nat_lit 6613, Int.ofNat (nat_lit 1))]
theorem atom2206Coded_decode : atom2206 = SparsePolynomial.decodeCubic 24 atom2206Coded := by decide +kernel
theorem atom2206Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) := by
  have h := atom2206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2207 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2207 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom2207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2207) := by
  rw [SparsePolynomial.eval_scale, eval_atom2207]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2207Coded : CoefficientMerge.Poly := [(nat_lit 6614, Int.ofNat (nat_lit 1))]
theorem atom2207Coded_decode : atom2207 = SparsePolynomial.decodeCubic 24 atom2207Coded := by decide +kernel
theorem atom2207Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) := by
  have h := atom2207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2208 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2208 = ((g 11) * (g 11) * (g 18)) := by
  norm_num [atom2208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11628748118592 : Int) atom2208) := by
  rw [SparsePolynomial.eval_scale, eval_atom2208]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2208Coded : CoefficientMerge.Poly := [(nat_lit 6618, Int.ofNat (nat_lit 1))]
theorem atom2208Coded_decode : atom2208 = SparsePolynomial.decodeCubic 24 atom2208Coded := by decide +kernel
theorem atom2208Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded) := by
  have h := atom2208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block029 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200)), (nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272)), (nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872)), (nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280)), (nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700)), (nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544)), (nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088)), (nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
def block029_data_flat000 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600))]
theorem block029_data_flat000_step : block029_data_flat000 = (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) := by decide +kernel
theorem block029_data_flat000_original : block029_data_flat000 = (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) := by
  rw [block029_data_flat000_step]
def block029_data_flat001 : CoefficientMerge.Poly := [(nat_lit 6060, Int.ofNat (nat_lit 11171370949200))]
theorem block029_data_flat001_step : block029_data_flat001 = (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded) := by decide +kernel
theorem block029_data_flat001_original : block029_data_flat001 = (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded) := by
  rw [block029_data_flat001_step]
def block029_data_flat002 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200))]
theorem block029_data_flat002_step : block029_data_flat002 = (CoefficientMerge.fastMerge block029_data_flat000 block029_data_flat001) := by decide +kernel
theorem block029_data_flat002_original : block029_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) := by
  rw [block029_data_flat002_step, block029_data_flat000_original, block029_data_flat001_original]
def block029_data_flat003 : CoefficientMerge.Poly := [(nat_lit 6061, Int.ofNat (nat_lit 15674337756000))]
theorem block029_data_flat003_step : block029_data_flat003 = (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) := by decide +kernel
theorem block029_data_flat003_original : block029_data_flat003 = (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) := by
  rw [block029_data_flat003_step]
def block029_data_flat004 : CoefficientMerge.Poly := [(nat_lit 6062, Int.ofNat (nat_lit 20819826165600))]
theorem block029_data_flat004_step : block029_data_flat004 = (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) := by decide +kernel
theorem block029_data_flat004_original : block029_data_flat004 = (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) := by
  rw [block029_data_flat004_step]
def block029_data_flat005 : CoefficientMerge.Poly := [(nat_lit 6063, Int.ofNat (nat_lit 25965314575200))]
theorem block029_data_flat005_step : block029_data_flat005 = (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded) := by decide +kernel
theorem block029_data_flat005_original : block029_data_flat005 = (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded) := by
  rw [block029_data_flat005_step]
def block029_data_flat006 : CoefficientMerge.Poly := [(nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200))]
theorem block029_data_flat006_step : block029_data_flat006 = (CoefficientMerge.fastMerge block029_data_flat004 block029_data_flat005) := by decide +kernel
theorem block029_data_flat006_original : block029_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)) := by
  rw [block029_data_flat006_step, block029_data_flat004_original, block029_data_flat005_original]
def block029_data_flat007 : CoefficientMerge.Poly := [(nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200))]
theorem block029_data_flat007_step : block029_data_flat007 = (CoefficientMerge.fastMerge block029_data_flat003 block029_data_flat006) := by decide +kernel
theorem block029_data_flat007_original : block029_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded))) := by
  rw [block029_data_flat007_step, block029_data_flat003_original, block029_data_flat006_original]
def block029_data_flat008 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200))]
theorem block029_data_flat008_step : block029_data_flat008 = (CoefficientMerge.fastMerge block029_data_flat002 block029_data_flat007) := by decide +kernel
theorem block029_data_flat008_original : block029_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) := by
  rw [block029_data_flat008_step, block029_data_flat002_original, block029_data_flat007_original]
def block029_data_flat009 : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 31110802984800))]
theorem block029_data_flat009_step : block029_data_flat009 = (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) := by decide +kernel
theorem block029_data_flat009_original : block029_data_flat009 = (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) := by
  rw [block029_data_flat009_step]
def block029_data_flat010 : CoefficientMerge.Poly := [(nat_lit 6065, Int.ofNat (nat_lit 36256291394400))]
theorem block029_data_flat010_step : block029_data_flat010 = (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded) := by decide +kernel
theorem block029_data_flat010_original : block029_data_flat010 = (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded) := by
  rw [block029_data_flat010_step]
def block029_data_flat011 : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400))]
theorem block029_data_flat011_step : block029_data_flat011 = (CoefficientMerge.fastMerge block029_data_flat009 block029_data_flat010) := by decide +kernel
theorem block029_data_flat011_original : block029_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) := by
  rw [block029_data_flat011_step, block029_data_flat009_original, block029_data_flat010_original]
def block029_data_flat012 : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 45334222105392))]
theorem block029_data_flat012_step : block029_data_flat012 = (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) := by decide +kernel
theorem block029_data_flat012_original : block029_data_flat012 = (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) := by
  rw [block029_data_flat012_step]
def block029_data_flat013 : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 62475180994512))]
theorem block029_data_flat013_step : block029_data_flat013 = (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) := by decide +kernel
theorem block029_data_flat013_original : block029_data_flat013 = (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) := by
  rw [block029_data_flat013_step]
def block029_data_flat014 : CoefficientMerge.Poly := [(nat_lit 6069, Int.ofNat (nat_lit 74122873486200))]
theorem block029_data_flat014_step : block029_data_flat014 = (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded) := by decide +kernel
theorem block029_data_flat014_original : block029_data_flat014 = (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded) := by
  rw [block029_data_flat014_step]
def block029_data_flat015 : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200))]
theorem block029_data_flat015_step : block029_data_flat015 = (CoefficientMerge.fastMerge block029_data_flat013 block029_data_flat014) := by decide +kernel
theorem block029_data_flat015_original : block029_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded)) := by
  rw [block029_data_flat015_step, block029_data_flat013_original, block029_data_flat014_original]
def block029_data_flat016 : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200))]
theorem block029_data_flat016_step : block029_data_flat016 = (CoefficientMerge.fastMerge block029_data_flat012 block029_data_flat015) := by decide +kernel
theorem block029_data_flat016_original : block029_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))) := by
  rw [block029_data_flat016_step, block029_data_flat012_original, block029_data_flat015_original]
def block029_data_flat017 : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200))]
theorem block029_data_flat017_step : block029_data_flat017 = (CoefficientMerge.fastMerge block029_data_flat011 block029_data_flat016) := by decide +kernel
theorem block029_data_flat017_original : block029_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded)))) := by
  rw [block029_data_flat017_step, block029_data_flat011_original, block029_data_flat016_original]
def block029_data_flat018 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200))]
theorem block029_data_flat018_step : block029_data_flat018 = (CoefficientMerge.fastMerge block029_data_flat008 block029_data_flat017) := by decide +kernel
theorem block029_data_flat018_original : block029_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) := by
  rw [block029_data_flat018_step, block029_data_flat008_original, block029_data_flat017_original]
def block029_data_flat019 : CoefficientMerge.Poly := [(nat_lit 6070, Int.ofNat (nat_lit 153208246292640))]
theorem block029_data_flat019_step : block029_data_flat019 = (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) := by decide +kernel
theorem block029_data_flat019_original : block029_data_flat019 = (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) := by
  rw [block029_data_flat019_step]
def block029_data_flat020 : CoefficientMerge.Poly := [(nat_lit 6071, Int.ofNat (nat_lit 247986262408500))]
theorem block029_data_flat020_step : block029_data_flat020 = (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded) := by decide +kernel
theorem block029_data_flat020_original : block029_data_flat020 = (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded) := by
  rw [block029_data_flat020_step]
def block029_data_flat021 : CoefficientMerge.Poly := [(nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500))]
theorem block029_data_flat021_step : block029_data_flat021 = (CoefficientMerge.fastMerge block029_data_flat019 block029_data_flat020) := by decide +kernel
theorem block029_data_flat021_original : block029_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) := by
  rw [block029_data_flat021_step, block029_data_flat019_original, block029_data_flat020_original]
def block029_data_flat022 : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 27104843581200))]
theorem block029_data_flat022_step : block029_data_flat022 = (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) := by decide +kernel
theorem block029_data_flat022_original : block029_data_flat022 = (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) := by
  rw [block029_data_flat022_step]
def block029_data_flat023 : CoefficientMerge.Poly := [(nat_lit 6086, Int.ofNat (nat_lit 48070183946400))]
theorem block029_data_flat023_step : block029_data_flat023 = (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) := by decide +kernel
theorem block029_data_flat023_original : block029_data_flat023 = (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) := by
  rw [block029_data_flat023_step]
def block029_data_flat024 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 51174486871200))]
theorem block029_data_flat024_step : block029_data_flat024 = (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded) := by decide +kernel
theorem block029_data_flat024_original : block029_data_flat024 = (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded) := by
  rw [block029_data_flat024_step]
def block029_data_flat025 : CoefficientMerge.Poly := [(nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200))]
theorem block029_data_flat025_step : block029_data_flat025 = (CoefficientMerge.fastMerge block029_data_flat023 block029_data_flat024) := by decide +kernel
theorem block029_data_flat025_original : block029_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)) := by
  rw [block029_data_flat025_step, block029_data_flat023_original, block029_data_flat024_original]
def block029_data_flat026 : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200))]
theorem block029_data_flat026_step : block029_data_flat026 = (CoefficientMerge.fastMerge block029_data_flat022 block029_data_flat025) := by decide +kernel
theorem block029_data_flat026_original : block029_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded))) := by
  rw [block029_data_flat026_step, block029_data_flat022_original, block029_data_flat025_original]
def block029_data_flat027 : CoefficientMerge.Poly := [(nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200))]
theorem block029_data_flat027_step : block029_data_flat027 = (CoefficientMerge.fastMerge block029_data_flat021 block029_data_flat026) := by decide +kernel
theorem block029_data_flat027_original : block029_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) := by
  rw [block029_data_flat027_step, block029_data_flat021_original, block029_data_flat026_original]
def block029_data_flat028 : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 57361830372000))]
theorem block029_data_flat028_step : block029_data_flat028 = (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) := by decide +kernel
theorem block029_data_flat028_original : block029_data_flat028 = (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) := by
  rw [block029_data_flat028_step]
def block029_data_flat029 : CoefficientMerge.Poly := [(nat_lit 6089, Int.ofNat (nat_lit 63549173872800))]
theorem block029_data_flat029_step : block029_data_flat029 = (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded) := by decide +kernel
theorem block029_data_flat029_original : block029_data_flat029 = (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded) := by
  rw [block029_data_flat029_step]
def block029_data_flat030 : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800))]
theorem block029_data_flat030_step : block029_data_flat030 = (CoefficientMerge.fastMerge block029_data_flat028 block029_data_flat029) := by decide +kernel
theorem block029_data_flat030_original : block029_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) := by
  rw [block029_data_flat030_step, block029_data_flat028_original, block029_data_flat029_original]
def block029_data_flat031 : CoefficientMerge.Poly := [(nat_lit 6090, Int.ofNat (nat_lit 73075050903888))]
theorem block029_data_flat031_step : block029_data_flat031 = (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) := by decide +kernel
theorem block029_data_flat031_original : block029_data_flat031 = (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) := by
  rw [block029_data_flat031_step]
def block029_data_flat032 : CoefficientMerge.Poly := [(nat_lit 6091, Int.ofNat (nat_lit 42531469390080))]
theorem block029_data_flat032_step : block029_data_flat032 = (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) := by decide +kernel
theorem block029_data_flat032_original : block029_data_flat032 = (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) := by
  rw [block029_data_flat032_step]
def block029_data_flat033 : CoefficientMerge.Poly := [(nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat033_step : block029_data_flat033 = (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded) := by decide +kernel
theorem block029_data_flat033_original : block029_data_flat033 = (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded) := by
  rw [block029_data_flat033_step]
def block029_data_flat034 : CoefficientMerge.Poly := [(nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat034_step : block029_data_flat034 = (CoefficientMerge.fastMerge block029_data_flat032 block029_data_flat033) := by decide +kernel
theorem block029_data_flat034_original : block029_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)) := by
  rw [block029_data_flat034_step, block029_data_flat032_original, block029_data_flat033_original]
def block029_data_flat035 : CoefficientMerge.Poly := [(nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat035_step : block029_data_flat035 = (CoefficientMerge.fastMerge block029_data_flat031 block029_data_flat034) := by decide +kernel
theorem block029_data_flat035_original : block029_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded))) := by
  rw [block029_data_flat035_step, block029_data_flat031_original, block029_data_flat034_original]
def block029_data_flat036 : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat036_step : block029_data_flat036 = (CoefficientMerge.fastMerge block029_data_flat030 block029_data_flat035) := by decide +kernel
theorem block029_data_flat036_original : block029_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))) := by
  rw [block029_data_flat036_step, block029_data_flat030_original, block029_data_flat035_original]
def block029_data_flat037 : CoefficientMerge.Poly := [(nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat037_step : block029_data_flat037 = (CoefficientMerge.fastMerge block029_data_flat027 block029_data_flat036) := by decide +kernel
theorem block029_data_flat037_original : block029_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded))))) := by
  rw [block029_data_flat037_step, block029_data_flat027_original, block029_data_flat036_original]
def block029_data_flat038 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200)), (nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272))]
theorem block029_data_flat038_step : block029_data_flat038 = (CoefficientMerge.fastMerge block029_data_flat018 block029_data_flat037) := by decide +kernel
theorem block029_data_flat038_original : block029_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) := by
  rw [block029_data_flat038_step, block029_data_flat018_original, block029_data_flat037_original]
def block029_data_flat039 : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 139283462035080))]
theorem block029_data_flat039_step : block029_data_flat039 = (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) := by decide +kernel
theorem block029_data_flat039_original : block029_data_flat039 = (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) := by
  rw [block029_data_flat039_step]
def block029_data_flat040 : CoefficientMerge.Poly := [(nat_lit 6094, Int.ofNat (nat_lit 231954760353888))]
theorem block029_data_flat040_step : block029_data_flat040 = (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded) := by decide +kernel
theorem block029_data_flat040_original : block029_data_flat040 = (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded) := by
  rw [block029_data_flat040_step]
def block029_data_flat041 : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888))]
theorem block029_data_flat041_step : block029_data_flat041 = (CoefficientMerge.fastMerge block029_data_flat039 block029_data_flat040) := by decide +kernel
theorem block029_data_flat041_original : block029_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) := by
  rw [block029_data_flat041_step, block029_data_flat039_original, block029_data_flat040_original]
def block029_data_flat042 : CoefficientMerge.Poly := [(nat_lit 6095, Int.ofNat (nat_lit 339742267533900))]
theorem block029_data_flat042_step : block029_data_flat042 = (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) := by decide +kernel
theorem block029_data_flat042_original : block029_data_flat042 = (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) := by
  rw [block029_data_flat042_step]
def block029_data_flat043 : CoefficientMerge.Poly := [(nat_lit 6110, Int.ofNat (nat_lit 43567217139600))]
theorem block029_data_flat043_step : block029_data_flat043 = (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) := by decide +kernel
theorem block029_data_flat043_original : block029_data_flat043 = (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) := by
  rw [block029_data_flat043_step]
def block029_data_flat044 : CoefficientMerge.Poly := [(nat_lit 6111, Int.ofNat (nat_lit 85125142317600))]
theorem block029_data_flat044_step : block029_data_flat044 = (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded) := by decide +kernel
theorem block029_data_flat044_original : block029_data_flat044 = (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded) := by
  rw [block029_data_flat044_step]
def block029_data_flat045 : CoefficientMerge.Poly := [(nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600))]
theorem block029_data_flat045_step : block029_data_flat045 = (CoefficientMerge.fastMerge block029_data_flat043 block029_data_flat044) := by decide +kernel
theorem block029_data_flat045_original : block029_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)) := by
  rw [block029_data_flat045_step, block029_data_flat043_original, block029_data_flat044_original]
def block029_data_flat046 : CoefficientMerge.Poly := [(nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600))]
theorem block029_data_flat046_step : block029_data_flat046 = (CoefficientMerge.fastMerge block029_data_flat042 block029_data_flat045) := by decide +kernel
theorem block029_data_flat046_original : block029_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded))) := by
  rw [block029_data_flat046_step, block029_data_flat042_original, block029_data_flat045_original]
def block029_data_flat047 : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600))]
theorem block029_data_flat047_step : block029_data_flat047 = (CoefficientMerge.fastMerge block029_data_flat041 block029_data_flat046) := by decide +kernel
theorem block029_data_flat047_original : block029_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) := by
  rw [block029_data_flat047_step, block029_data_flat041_original, block029_data_flat046_original]
def block029_data_flat048 : CoefficientMerge.Poly := [(nat_lit 6112, Int.ofNat (nat_lit 91333748167200))]
theorem block029_data_flat048_step : block029_data_flat048 = (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) := by decide +kernel
theorem block029_data_flat048_original : block029_data_flat048 = (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) := by
  rw [block029_data_flat048_step]
def block029_data_flat049 : CoefficientMerge.Poly := [(nat_lit 6113, Int.ofNat (nat_lit 97542354016800))]
theorem block029_data_flat049_step : block029_data_flat049 = (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded) := by decide +kernel
theorem block029_data_flat049_original : block029_data_flat049 = (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded) := by
  rw [block029_data_flat049_step]
def block029_data_flat050 : CoefficientMerge.Poly := [(nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800))]
theorem block029_data_flat050_step : block029_data_flat050 = (CoefficientMerge.fastMerge block029_data_flat048 block029_data_flat049) := by decide +kernel
theorem block029_data_flat050_original : block029_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) := by
  rw [block029_data_flat050_step, block029_data_flat048_original, block029_data_flat049_original]
def block029_data_flat051 : CoefficientMerge.Poly := [(nat_lit 6114, Int.ofNat (nat_lit 98659441119888))]
theorem block029_data_flat051_step : block029_data_flat051 = (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) := by decide +kernel
theorem block029_data_flat051_original : block029_data_flat051 = (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) := by
  rw [block029_data_flat051_step]
def block029_data_flat052 : CoefficientMerge.Poly := [(nat_lit 6115, Int.ofNat (nat_lit 89005622222880))]
theorem block029_data_flat052_step : block029_data_flat052 = (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) := by decide +kernel
theorem block029_data_flat052_original : block029_data_flat052 = (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) := by
  rw [block029_data_flat052_step]
def block029_data_flat053 : CoefficientMerge.Poly := [(nat_lit 6116, Int.ofNat (nat_lit 181911628693872))]
theorem block029_data_flat053_step : block029_data_flat053 = (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded) := by decide +kernel
theorem block029_data_flat053_original : block029_data_flat053 = (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded) := by
  rw [block029_data_flat053_step]
def block029_data_flat054 : CoefficientMerge.Poly := [(nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872))]
theorem block029_data_flat054_step : block029_data_flat054 = (CoefficientMerge.fastMerge block029_data_flat052 block029_data_flat053) := by decide +kernel
theorem block029_data_flat054_original : block029_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded)) := by
  rw [block029_data_flat054_step, block029_data_flat052_original, block029_data_flat053_original]
def block029_data_flat055 : CoefficientMerge.Poly := [(nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872))]
theorem block029_data_flat055_step : block029_data_flat055 = (CoefficientMerge.fastMerge block029_data_flat051 block029_data_flat054) := by decide +kernel
theorem block029_data_flat055_original : block029_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))) := by
  rw [block029_data_flat055_step, block029_data_flat051_original, block029_data_flat054_original]
def block029_data_flat056 : CoefficientMerge.Poly := [(nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872))]
theorem block029_data_flat056_step : block029_data_flat056 = (CoefficientMerge.fastMerge block029_data_flat050 block029_data_flat055) := by decide +kernel
theorem block029_data_flat056_original : block029_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded)))) := by
  rw [block029_data_flat056_step, block029_data_flat050_original, block029_data_flat055_original]
def block029_data_flat057 : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872))]
theorem block029_data_flat057_step : block029_data_flat057 = (CoefficientMerge.fastMerge block029_data_flat047 block029_data_flat056) := by decide +kernel
theorem block029_data_flat057_original : block029_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) := by
  rw [block029_data_flat057_step, block029_data_flat047_original, block029_data_flat056_original]
def block029_data_flat058 : CoefficientMerge.Poly := [(nat_lit 6117, Int.ofNat (nat_lit 210902114186280))]
theorem block029_data_flat058_step : block029_data_flat058 = (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) := by decide +kernel
theorem block029_data_flat058_original : block029_data_flat058 = (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) := by
  rw [block029_data_flat058_step]
def block029_data_flat059 : CoefficientMerge.Poly := [(nat_lit 6118, Int.ofNat (nat_lit 296892084189888))]
theorem block029_data_flat059_step : block029_data_flat059 = (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded) := by decide +kernel
theorem block029_data_flat059_original : block029_data_flat059 = (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded) := by
  rw [block029_data_flat059_step]
def block029_data_flat060 : CoefficientMerge.Poly := [(nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888))]
theorem block029_data_flat060_step : block029_data_flat060 = (CoefficientMerge.fastMerge block029_data_flat058 block029_data_flat059) := by decide +kernel
theorem block029_data_flat060_original : block029_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) := by
  rw [block029_data_flat060_step, block029_data_flat058_original, block029_data_flat059_original]
def block029_data_flat061 : CoefficientMerge.Poly := [(nat_lit 6119, Int.ofNat (nat_lit 409342572985500))]
theorem block029_data_flat061_step : block029_data_flat061 = (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) := by decide +kernel
theorem block029_data_flat061_original : block029_data_flat061 = (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) := by
  rw [block029_data_flat061_step]
def block029_data_flat062 : CoefficientMerge.Poly := [(nat_lit 6135, Int.ofNat (nat_lit 67242842528400))]
theorem block029_data_flat062_step : block029_data_flat062 = (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) := by decide +kernel
theorem block029_data_flat062_original : block029_data_flat062 = (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) := by
  rw [block029_data_flat062_step]
def block029_data_flat063 : CoefficientMerge.Poly := [(nat_lit 6136, Int.ofNat (nat_lit 126342205466400))]
theorem block029_data_flat063_step : block029_data_flat063 = (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded) := by decide +kernel
theorem block029_data_flat063_original : block029_data_flat063 = (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded) := by
  rw [block029_data_flat063_step]
def block029_data_flat064 : CoefficientMerge.Poly := [(nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400))]
theorem block029_data_flat064_step : block029_data_flat064 = (CoefficientMerge.fastMerge block029_data_flat062 block029_data_flat063) := by decide +kernel
theorem block029_data_flat064_original : block029_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)) := by
  rw [block029_data_flat064_step, block029_data_flat062_original, block029_data_flat063_original]
def block029_data_flat065 : CoefficientMerge.Poly := [(nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400))]
theorem block029_data_flat065_step : block029_data_flat065 = (CoefficientMerge.fastMerge block029_data_flat061 block029_data_flat064) := by decide +kernel
theorem block029_data_flat065_original : block029_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded))) := by
  rw [block029_data_flat065_step, block029_data_flat061_original, block029_data_flat064_original]
def block029_data_flat066 : CoefficientMerge.Poly := [(nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400))]
theorem block029_data_flat066_step : block029_data_flat066 = (CoefficientMerge.fastMerge block029_data_flat060 block029_data_flat065) := by decide +kernel
theorem block029_data_flat066_original : block029_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) := by
  rw [block029_data_flat066_step, block029_data_flat060_original, block029_data_flat065_original]
def block029_data_flat067 : CoefficientMerge.Poly := [(nat_lit 6137, Int.ofNat (nat_lit 131551480922400))]
theorem block029_data_flat067_step : block029_data_flat067 = (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) := by decide +kernel
theorem block029_data_flat067_original : block029_data_flat067 = (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) := by
  rw [block029_data_flat067_step]
def block029_data_flat068 : CoefficientMerge.Poly := [(nat_lit 6138, Int.ofNat (nat_lit 146424341228688))]
theorem block029_data_flat068_step : block029_data_flat068 = (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded) := by decide +kernel
theorem block029_data_flat068_original : block029_data_flat068 = (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded) := by
  rw [block029_data_flat068_step]
def block029_data_flat069 : CoefficientMerge.Poly := [(nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688))]
theorem block029_data_flat069_step : block029_data_flat069 = (CoefficientMerge.fastMerge block029_data_flat067 block029_data_flat068) := by decide +kernel
theorem block029_data_flat069_original : block029_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) := by
  rw [block029_data_flat069_step, block029_data_flat067_original, block029_data_flat068_original]
def block029_data_flat070 : CoefficientMerge.Poly := [(nat_lit 6139, Int.ofNat (nat_lit 141191439828480))]
theorem block029_data_flat070_step : block029_data_flat070 = (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) := by decide +kernel
theorem block029_data_flat070_original : block029_data_flat070 = (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) := by
  rw [block029_data_flat070_step]
def block029_data_flat071 : CoefficientMerge.Poly := [(nat_lit 6140, Int.ofNat (nat_lit 276800336879472))]
theorem block029_data_flat071_step : block029_data_flat071 = (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) := by decide +kernel
theorem block029_data_flat071_original : block029_data_flat071 = (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) := by
  rw [block029_data_flat071_step]
def block029_data_flat072 : CoefficientMerge.Poly := [(nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat072_step : block029_data_flat072 = (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded) := by decide +kernel
theorem block029_data_flat072_original : block029_data_flat072 = (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded) := by
  rw [block029_data_flat072_step]
def block029_data_flat073 : CoefficientMerge.Poly := [(nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat073_step : block029_data_flat073 = (CoefficientMerge.fastMerge block029_data_flat071 block029_data_flat072) := by decide +kernel
theorem block029_data_flat073_original : block029_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded)) := by
  rw [block029_data_flat073_step, block029_data_flat071_original, block029_data_flat072_original]
def block029_data_flat074 : CoefficientMerge.Poly := [(nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat074_step : block029_data_flat074 = (CoefficientMerge.fastMerge block029_data_flat070 block029_data_flat073) := by decide +kernel
theorem block029_data_flat074_original : block029_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))) := by
  rw [block029_data_flat074_step, block029_data_flat070_original, block029_data_flat073_original]
def block029_data_flat075 : CoefficientMerge.Poly := [(nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat075_step : block029_data_flat075 = (CoefficientMerge.fastMerge block029_data_flat069 block029_data_flat074) := by decide +kernel
theorem block029_data_flat075_original : block029_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded)))) := by
  rw [block029_data_flat075_step, block029_data_flat069_original, block029_data_flat074_original]
def block029_data_flat076 : CoefficientMerge.Poly := [(nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat076_step : block029_data_flat076 = (CoefficientMerge.fastMerge block029_data_flat066 block029_data_flat075) := by decide +kernel
theorem block029_data_flat076_original : block029_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))) := by
  rw [block029_data_flat076_step, block029_data_flat066_original, block029_data_flat075_original]
def block029_data_flat077 : CoefficientMerge.Poly := [(nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872)), (nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat077_step : block029_data_flat077 = (CoefficientMerge.fastMerge block029_data_flat057 block029_data_flat076) := by decide +kernel
theorem block029_data_flat077_original : block029_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded)))))) := by
  rw [block029_data_flat077_step, block029_data_flat057_original, block029_data_flat076_original]
def block029_data_flat078 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200)), (nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272)), (nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872)), (nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280))]
theorem block029_data_flat078_step : block029_data_flat078 = (CoefficientMerge.fastMerge block029_data_flat038 block029_data_flat077) := by decide +kernel
theorem block029_data_flat078_original : block029_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))))) := by
  rw [block029_data_flat078_step, block029_data_flat038_original, block029_data_flat077_original]
def block029_data_flat079 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688))]
theorem block029_data_flat079_step : block029_data_flat079 = (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) := by decide +kernel
theorem block029_data_flat079_original : block029_data_flat079 = (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) := by
  rw [block029_data_flat079_step]
def block029_data_flat080 : CoefficientMerge.Poly := [(nat_lit 6143, Int.ofNat (nat_lit 469518281927100))]
theorem block029_data_flat080_step : block029_data_flat080 = (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded) := by decide +kernel
theorem block029_data_flat080_original : block029_data_flat080 = (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded) := by
  rw [block029_data_flat080_step]
def block029_data_flat081 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100))]
theorem block029_data_flat081_step : block029_data_flat081 = (CoefficientMerge.fastMerge block029_data_flat079 block029_data_flat080) := by decide +kernel
theorem block029_data_flat081_original : block029_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) := by
  rw [block029_data_flat081_step, block029_data_flat079_original, block029_data_flat080_original]
def block029_data_flat082 : CoefficientMerge.Poly := [(nat_lit 6160, Int.ofNat (nat_lit 87867320864400))]
theorem block029_data_flat082_step : block029_data_flat082 = (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) := by decide +kernel
theorem block029_data_flat082_original : block029_data_flat082 = (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) := by
  rw [block029_data_flat082_step]
def block029_data_flat083 : CoefficientMerge.Poly := [(nat_lit 6161, Int.ofNat (nat_lit 175840953472800))]
theorem block029_data_flat083_step : block029_data_flat083 = (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) := by decide +kernel
theorem block029_data_flat083_original : block029_data_flat083 = (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) := by
  rw [block029_data_flat083_step]
def block029_data_flat084 : CoefficientMerge.Poly := [(nat_lit 6162, Int.ofNat (nat_lit 176455475967888))]
theorem block029_data_flat084_step : block029_data_flat084 = (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded) := by decide +kernel
theorem block029_data_flat084_original : block029_data_flat084 = (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded) := by
  rw [block029_data_flat084_step]
def block029_data_flat085 : CoefficientMerge.Poly := [(nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888))]
theorem block029_data_flat085_step : block029_data_flat085 = (CoefficientMerge.fastMerge block029_data_flat083 block029_data_flat084) := by decide +kernel
theorem block029_data_flat085_original : block029_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)) := by
  rw [block029_data_flat085_step, block029_data_flat083_original, block029_data_flat084_original]
def block029_data_flat086 : CoefficientMerge.Poly := [(nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888))]
theorem block029_data_flat086_step : block029_data_flat086 = (CoefficientMerge.fastMerge block029_data_flat082 block029_data_flat085) := by decide +kernel
theorem block029_data_flat086_original : block029_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded))) := by
  rw [block029_data_flat086_step, block029_data_flat082_original, block029_data_flat085_original]
def block029_data_flat087 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888))]
theorem block029_data_flat087_step : block029_data_flat087 = (CoefficientMerge.fastMerge block029_data_flat081 block029_data_flat086) := by decide +kernel
theorem block029_data_flat087_original : block029_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) := by
  rw [block029_data_flat087_step, block029_data_flat081_original, block029_data_flat086_original]
def block029_data_flat088 : CoefficientMerge.Poly := [(nat_lit 6163, Int.ofNat (nat_lit 188873223482880))]
theorem block029_data_flat088_step : block029_data_flat088 = (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) := by decide +kernel
theorem block029_data_flat088_original : block029_data_flat088 = (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) := by
  rw [block029_data_flat088_step]
def block029_data_flat089 : CoefficientMerge.Poly := [(nat_lit 6164, Int.ofNat (nat_lit 342132769449072))]
theorem block029_data_flat089_step : block029_data_flat089 = (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded) := by decide +kernel
theorem block029_data_flat089_original : block029_data_flat089 = (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded) := by
  rw [block029_data_flat089_step]
def block029_data_flat090 : CoefficientMerge.Poly := [(nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072))]
theorem block029_data_flat090_step : block029_data_flat090 = (CoefficientMerge.fastMerge block029_data_flat088 block029_data_flat089) := by decide +kernel
theorem block029_data_flat090_original : block029_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) := by
  rw [block029_data_flat090_step, block029_data_flat088_original, block029_data_flat089_original]
def block029_data_flat091 : CoefficientMerge.Poly := [(nat_lit 6165, Int.ofNat (nat_lit 402956051584680))]
theorem block029_data_flat091_step : block029_data_flat091 = (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) := by decide +kernel
theorem block029_data_flat091_original : block029_data_flat091 = (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) := by
  rw [block029_data_flat091_step]
def block029_data_flat092 : CoefficientMerge.Poly := [(nat_lit 6166, Int.ofNat (nat_lit 392182562174688))]
theorem block029_data_flat092_step : block029_data_flat092 = (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) := by decide +kernel
theorem block029_data_flat092_original : block029_data_flat092 = (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) := by
  rw [block029_data_flat092_step]
def block029_data_flat093 : CoefficientMerge.Poly := [(nat_lit 6167, Int.ofNat (nat_lit 595302229928700))]
theorem block029_data_flat093_step : block029_data_flat093 = (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded) := by decide +kernel
theorem block029_data_flat093_original : block029_data_flat093 = (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded) := by
  rw [block029_data_flat093_step]
def block029_data_flat094 : CoefficientMerge.Poly := [(nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700))]
theorem block029_data_flat094_step : block029_data_flat094 = (CoefficientMerge.fastMerge block029_data_flat092 block029_data_flat093) := by decide +kernel
theorem block029_data_flat094_original : block029_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded)) := by
  rw [block029_data_flat094_step, block029_data_flat092_original, block029_data_flat093_original]
def block029_data_flat095 : CoefficientMerge.Poly := [(nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700))]
theorem block029_data_flat095_step : block029_data_flat095 = (CoefficientMerge.fastMerge block029_data_flat091 block029_data_flat094) := by decide +kernel
theorem block029_data_flat095_original : block029_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))) := by
  rw [block029_data_flat095_step, block029_data_flat091_original, block029_data_flat094_original]
def block029_data_flat096 : CoefficientMerge.Poly := [(nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700))]
theorem block029_data_flat096_step : block029_data_flat096 = (CoefficientMerge.fastMerge block029_data_flat090 block029_data_flat095) := by decide +kernel
theorem block029_data_flat096_original : block029_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded)))) := by
  rw [block029_data_flat096_step, block029_data_flat090_original, block029_data_flat095_original]
def block029_data_flat097 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700))]
theorem block029_data_flat097_step : block029_data_flat097 = (CoefficientMerge.fastMerge block029_data_flat087 block029_data_flat096) := by decide +kernel
theorem block029_data_flat097_original : block029_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) := by
  rw [block029_data_flat097_step, block029_data_flat087_original, block029_data_flat096_original]
def block029_data_flat098 : CoefficientMerge.Poly := [(nat_lit 6185, Int.ofNat (nat_lit 111950474605200))]
theorem block029_data_flat098_step : block029_data_flat098 = (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) := by decide +kernel
theorem block029_data_flat098_original : block029_data_flat098 = (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) := by
  rw [block029_data_flat098_step]
def block029_data_flat099 : CoefficientMerge.Poly := [(nat_lit 6186, Int.ofNat (nat_lit 221385718393488))]
theorem block029_data_flat099_step : block029_data_flat099 = (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded) := by decide +kernel
theorem block029_data_flat099_original : block029_data_flat099 = (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded) := by
  rw [block029_data_flat099_step]
def block029_data_flat100 : CoefficientMerge.Poly := [(nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488))]
theorem block029_data_flat100_step : block029_data_flat100 = (CoefficientMerge.fastMerge block029_data_flat098 block029_data_flat099) := by decide +kernel
theorem block029_data_flat100_original : block029_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) := by
  rw [block029_data_flat100_step, block029_data_flat098_original, block029_data_flat099_original]
def block029_data_flat101 : CoefficientMerge.Poly := [(nat_lit 6187, Int.ofNat (nat_lit 256420484052480))]
theorem block029_data_flat101_step : block029_data_flat101 = (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) := by decide +kernel
theorem block029_data_flat101_original : block029_data_flat101 = (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) := by
  rw [block029_data_flat101_step]
def block029_data_flat102 : CoefficientMerge.Poly := [(nat_lit 6188, Int.ofNat (nat_lit 432297048162672))]
theorem block029_data_flat102_step : block029_data_flat102 = (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) := by decide +kernel
theorem block029_data_flat102_original : block029_data_flat102 = (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) := by
  rw [block029_data_flat102_step]
def block029_data_flat103 : CoefficientMerge.Poly := [(nat_lit 6189, Int.ofNat (nat_lit 510042099453480))]
theorem block029_data_flat103_step : block029_data_flat103 = (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded) := by decide +kernel
theorem block029_data_flat103_original : block029_data_flat103 = (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded) := by
  rw [block029_data_flat103_step]
def block029_data_flat104 : CoefficientMerge.Poly := [(nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480))]
theorem block029_data_flat104_step : block029_data_flat104 = (CoefficientMerge.fastMerge block029_data_flat102 block029_data_flat103) := by decide +kernel
theorem block029_data_flat104_original : block029_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)) := by
  rw [block029_data_flat104_step, block029_data_flat102_original, block029_data_flat103_original]
def block029_data_flat105 : CoefficientMerge.Poly := [(nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480))]
theorem block029_data_flat105_step : block029_data_flat105 = (CoefficientMerge.fastMerge block029_data_flat101 block029_data_flat104) := by decide +kernel
theorem block029_data_flat105_original : block029_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded))) := by
  rw [block029_data_flat105_step, block029_data_flat101_original, block029_data_flat104_original]
def block029_data_flat106 : CoefficientMerge.Poly := [(nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480))]
theorem block029_data_flat106_step : block029_data_flat106 = (CoefficientMerge.fastMerge block029_data_flat100 block029_data_flat105) := by decide +kernel
theorem block029_data_flat106_original : block029_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) := by
  rw [block029_data_flat106_step, block029_data_flat100_original, block029_data_flat105_original]
def block029_data_flat107 : CoefficientMerge.Poly := [(nat_lit 6190, Int.ofNat (nat_lit 515066696280288))]
theorem block029_data_flat107_step : block029_data_flat107 = (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) := by decide +kernel
theorem block029_data_flat107_original : block029_data_flat107 = (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) := by
  rw [block029_data_flat107_step]
def block029_data_flat108 : CoefficientMerge.Poly := [(nat_lit 6191, Int.ofNat (nat_lit 732260508695100))]
theorem block029_data_flat108_step : block029_data_flat108 = (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded) := by decide +kernel
theorem block029_data_flat108_original : block029_data_flat108 = (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded) := by
  rw [block029_data_flat108_step]
def block029_data_flat109 : CoefficientMerge.Poly := [(nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100))]
theorem block029_data_flat109_step : block029_data_flat109 = (CoefficientMerge.fastMerge block029_data_flat107 block029_data_flat108) := by decide +kernel
theorem block029_data_flat109_original : block029_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) := by
  rw [block029_data_flat109_step, block029_data_flat107_original, block029_data_flat108_original]
def block029_data_flat110 : CoefficientMerge.Poly := [(nat_lit 6210, Int.ofNat (nat_lit 155797451099136))]
theorem block029_data_flat110_step : block029_data_flat110 = (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) := by decide +kernel
theorem block029_data_flat110_original : block029_data_flat110 = (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) := by
  rw [block029_data_flat110_step]
def block029_data_flat111 : CoefficientMerge.Poly := [(nat_lit 6211, Int.ofNat (nat_lit 337443300433008))]
theorem block029_data_flat111_step : block029_data_flat111 = (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) := by decide +kernel
theorem block029_data_flat111_original : block029_data_flat111 = (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) := by
  rw [block029_data_flat111_step]
def block029_data_flat112 : CoefficientMerge.Poly := [(nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat112_step : block029_data_flat112 = (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded) := by decide +kernel
theorem block029_data_flat112_original : block029_data_flat112 = (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded) := by
  rw [block029_data_flat112_step]
def block029_data_flat113 : CoefficientMerge.Poly := [(nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat113_step : block029_data_flat113 = (CoefficientMerge.fastMerge block029_data_flat111 block029_data_flat112) := by decide +kernel
theorem block029_data_flat113_original : block029_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)) := by
  rw [block029_data_flat113_step, block029_data_flat111_original, block029_data_flat112_original]
def block029_data_flat114 : CoefficientMerge.Poly := [(nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat114_step : block029_data_flat114 = (CoefficientMerge.fastMerge block029_data_flat110 block029_data_flat113) := by decide +kernel
theorem block029_data_flat114_original : block029_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded))) := by
  rw [block029_data_flat114_step, block029_data_flat110_original, block029_data_flat113_original]
def block029_data_flat115 : CoefficientMerge.Poly := [(nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat115_step : block029_data_flat115 = (CoefficientMerge.fastMerge block029_data_flat109 block029_data_flat114) := by decide +kernel
theorem block029_data_flat115_original : block029_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))) := by
  rw [block029_data_flat115_step, block029_data_flat109_original, block029_data_flat114_original]
def block029_data_flat116 : CoefficientMerge.Poly := [(nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat116_step : block029_data_flat116 = (CoefficientMerge.fastMerge block029_data_flat106 block029_data_flat115) := by decide +kernel
theorem block029_data_flat116_original : block029_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded))))) := by
  rw [block029_data_flat116_step, block029_data_flat106_original, block029_data_flat115_original]
def block029_data_flat117 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700)), (nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544))]
theorem block029_data_flat117_step : block029_data_flat117 = (CoefficientMerge.fastMerge block029_data_flat097 block029_data_flat116) := by decide +kernel
theorem block029_data_flat117_original : block029_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) := by
  rw [block029_data_flat117_step, block029_data_flat097_original, block029_data_flat116_original]
def block029_data_flat118 : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 618751227702168))]
theorem block029_data_flat118_step : block029_data_flat118 = (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) := by decide +kernel
theorem block029_data_flat118_original : block029_data_flat118 = (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) := by
  rw [block029_data_flat118_step]
def block029_data_flat119 : CoefficientMerge.Poly := [(nat_lit 6214, Int.ofNat (nat_lit 510055392621024))]
theorem block029_data_flat119_step : block029_data_flat119 = (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded) := by decide +kernel
theorem block029_data_flat119_original : block029_data_flat119 = (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded) := by
  rw [block029_data_flat119_step]
def block029_data_flat120 : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024))]
theorem block029_data_flat120_step : block029_data_flat120 = (CoefficientMerge.fastMerge block029_data_flat118 block029_data_flat119) := by decide +kernel
theorem block029_data_flat120_original : block029_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) := by
  rw [block029_data_flat120_step, block029_data_flat118_original, block029_data_flat119_original]
def block029_data_flat121 : CoefficientMerge.Poly := [(nat_lit 6215, Int.ofNat (nat_lit 755578774750140))]
theorem block029_data_flat121_step : block029_data_flat121 = (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) := by decide +kernel
theorem block029_data_flat121_original : block029_data_flat121 = (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) := by
  rw [block029_data_flat121_step]
def block029_data_flat122 : CoefficientMerge.Poly := [(nat_lit 6235, Int.ofNat (nat_lit 118417314212208))]
theorem block029_data_flat122_step : block029_data_flat122 = (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) := by decide +kernel
theorem block029_data_flat122_original : block029_data_flat122 = (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) := by
  rw [block029_data_flat122_step]
def block029_data_flat123 : CoefficientMerge.Poly := [(nat_lit 6236, Int.ofNat (nat_lit 457772204848464))]
theorem block029_data_flat123_step : block029_data_flat123 = (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded) := by decide +kernel
theorem block029_data_flat123_original : block029_data_flat123 = (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded) := by
  rw [block029_data_flat123_step]
def block029_data_flat124 : CoefficientMerge.Poly := [(nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464))]
theorem block029_data_flat124_step : block029_data_flat124 = (CoefficientMerge.fastMerge block029_data_flat122 block029_data_flat123) := by decide +kernel
theorem block029_data_flat124_original : block029_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)) := by
  rw [block029_data_flat124_step, block029_data_flat122_original, block029_data_flat123_original]
def block029_data_flat125 : CoefficientMerge.Poly := [(nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464))]
theorem block029_data_flat125_step : block029_data_flat125 = (CoefficientMerge.fastMerge block029_data_flat121 block029_data_flat124) := by decide +kernel
theorem block029_data_flat125_original : block029_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded))) := by
  rw [block029_data_flat125_step, block029_data_flat121_original, block029_data_flat124_original]
def block029_data_flat126 : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464))]
theorem block029_data_flat126_step : block029_data_flat126 = (CoefficientMerge.fastMerge block029_data_flat120 block029_data_flat125) := by decide +kernel
theorem block029_data_flat126_original : block029_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) := by
  rw [block029_data_flat126_step, block029_data_flat120_original, block029_data_flat125_original]
def block029_data_flat127 : CoefficientMerge.Poly := [(nat_lit 6237, Int.ofNat (nat_lit 509935380181128))]
theorem block029_data_flat127_step : block029_data_flat127 = (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) := by decide +kernel
theorem block029_data_flat127_original : block029_data_flat127 = (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) := by
  rw [block029_data_flat127_step]
def block029_data_flat128 : CoefficientMerge.Poly := [(nat_lit 6238, Int.ofNat (nat_lit 417231228435936))]
theorem block029_data_flat128_step : block029_data_flat128 = (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded) := by decide +kernel
theorem block029_data_flat128_original : block029_data_flat128 = (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded) := by
  rw [block029_data_flat128_step]
def block029_data_flat129 : CoefficientMerge.Poly := [(nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936))]
theorem block029_data_flat129_step : block029_data_flat129 = (CoefficientMerge.fastMerge block029_data_flat127 block029_data_flat128) := by decide +kernel
theorem block029_data_flat129_original : block029_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) := by
  rw [block029_data_flat129_step, block029_data_flat127_original, block029_data_flat128_original]
def block029_data_flat130 : CoefficientMerge.Poly := [(nat_lit 6239, Int.ofNat (nat_lit 516076854392700))]
theorem block029_data_flat130_step : block029_data_flat130 = (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) := by decide +kernel
theorem block029_data_flat130_original : block029_data_flat130 = (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) := by
  rw [block029_data_flat130_step]
def block029_data_flat131 : CoefficientMerge.Poly := [(nat_lit 6260, Int.ofNat (nat_lit 346547254740192))]
theorem block029_data_flat131_step : block029_data_flat131 = (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) := by decide +kernel
theorem block029_data_flat131_original : block029_data_flat131 = (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) := by
  rw [block029_data_flat131_step]
def block029_data_flat132 : CoefficientMerge.Poly := [(nat_lit 6261, Int.ofNat (nat_lit 577171780724088))]
theorem block029_data_flat132_step : block029_data_flat132 = (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded) := by decide +kernel
theorem block029_data_flat132_original : block029_data_flat132 = (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded) := by
  rw [block029_data_flat132_step]
def block029_data_flat133 : CoefficientMerge.Poly := [(nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088))]
theorem block029_data_flat133_step : block029_data_flat133 = (CoefficientMerge.fastMerge block029_data_flat131 block029_data_flat132) := by decide +kernel
theorem block029_data_flat133_original : block029_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded)) := by
  rw [block029_data_flat133_step, block029_data_flat131_original, block029_data_flat132_original]
def block029_data_flat134 : CoefficientMerge.Poly := [(nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088))]
theorem block029_data_flat134_step : block029_data_flat134 = (CoefficientMerge.fastMerge block029_data_flat130 block029_data_flat133) := by decide +kernel
theorem block029_data_flat134_original : block029_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))) := by
  rw [block029_data_flat134_step, block029_data_flat130_original, block029_data_flat133_original]
def block029_data_flat135 : CoefficientMerge.Poly := [(nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088))]
theorem block029_data_flat135_step : block029_data_flat135 = (CoefficientMerge.fastMerge block029_data_flat129 block029_data_flat134) := by decide +kernel
theorem block029_data_flat135_original : block029_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded)))) := by
  rw [block029_data_flat135_step, block029_data_flat129_original, block029_data_flat134_original]
def block029_data_flat136 : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088))]
theorem block029_data_flat136_step : block029_data_flat136 = (CoefficientMerge.fastMerge block029_data_flat126 block029_data_flat135) := by decide +kernel
theorem block029_data_flat136_original : block029_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) := by
  rw [block029_data_flat136_step, block029_data_flat126_original, block029_data_flat135_original]
def block029_data_flat137 : CoefficientMerge.Poly := [(nat_lit 6262, Int.ofNat (nat_lit 437315251001568))]
theorem block029_data_flat137_step : block029_data_flat137 = (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) := by decide +kernel
theorem block029_data_flat137_original : block029_data_flat137 = (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) := by
  rw [block029_data_flat137_step]
def block029_data_flat138 : CoefficientMerge.Poly := [(nat_lit 6263, Int.ofNat (nat_lit 473142522455676))]
theorem block029_data_flat138_step : block029_data_flat138 = (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded) := by decide +kernel
theorem block029_data_flat138_original : block029_data_flat138 = (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded) := by
  rw [block029_data_flat138_step]
def block029_data_flat139 : CoefficientMerge.Poly := [(nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676))]
theorem block029_data_flat139_step : block029_data_flat139 = (CoefficientMerge.fastMerge block029_data_flat137 block029_data_flat138) := by decide +kernel
theorem block029_data_flat139_original : block029_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) := by
  rw [block029_data_flat139_step, block029_data_flat137_original, block029_data_flat138_original]
def block029_data_flat140 : CoefficientMerge.Poly := [(nat_lit 6285, Int.ofNat (nat_lit 169648736717592))]
theorem block029_data_flat140_step : block029_data_flat140 = (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) := by decide +kernel
theorem block029_data_flat140_original : block029_data_flat140 = (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) := by
  rw [block029_data_flat140_step]
def block029_data_flat141 : CoefficientMerge.Poly := [(nat_lit 6286, Int.ofNat (nat_lit 230976346924512))]
theorem block029_data_flat141_step : block029_data_flat141 = (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) := by decide +kernel
theorem block029_data_flat141_original : block029_data_flat141 = (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) := by
  rw [block029_data_flat141_step]
def block029_data_flat142 : CoefficientMerge.Poly := [(nat_lit 6287, Int.ofNat (nat_lit 260856825525180))]
theorem block029_data_flat142_step : block029_data_flat142 = (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded) := by decide +kernel
theorem block029_data_flat142_original : block029_data_flat142 = (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded) := by
  rw [block029_data_flat142_step]
def block029_data_flat143 : CoefficientMerge.Poly := [(nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180))]
theorem block029_data_flat143_step : block029_data_flat143 = (CoefficientMerge.fastMerge block029_data_flat141 block029_data_flat142) := by decide +kernel
theorem block029_data_flat143_original : block029_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)) := by
  rw [block029_data_flat143_step, block029_data_flat141_original, block029_data_flat142_original]
def block029_data_flat144 : CoefficientMerge.Poly := [(nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180))]
theorem block029_data_flat144_step : block029_data_flat144 = (CoefficientMerge.fastMerge block029_data_flat140 block029_data_flat143) := by decide +kernel
theorem block029_data_flat144_original : block029_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded))) := by
  rw [block029_data_flat144_step, block029_data_flat140_original, block029_data_flat143_original]
def block029_data_flat145 : CoefficientMerge.Poly := [(nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180))]
theorem block029_data_flat145_step : block029_data_flat145 = (CoefficientMerge.fastMerge block029_data_flat139 block029_data_flat144) := by decide +kernel
theorem block029_data_flat145_original : block029_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) := by
  rw [block029_data_flat145_step, block029_data_flat139_original, block029_data_flat144_original]
def block029_data_flat146 : CoefficientMerge.Poly := [(nat_lit 6611, Int.ofNat (nat_lit 10703377792800))]
theorem block029_data_flat146_step : block029_data_flat146 = (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) := by decide +kernel
theorem block029_data_flat146_original : block029_data_flat146 = (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) := by
  rw [block029_data_flat146_step]
def block029_data_flat147 : CoefficientMerge.Poly := [(nat_lit 6612, Int.ofNat (nat_lit 9249121728000))]
theorem block029_data_flat147_step : block029_data_flat147 = (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded) := by decide +kernel
theorem block029_data_flat147_original : block029_data_flat147 = (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded) := by
  rw [block029_data_flat147_step]
def block029_data_flat148 : CoefficientMerge.Poly := [(nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000))]
theorem block029_data_flat148_step : block029_data_flat148 = (CoefficientMerge.fastMerge block029_data_flat146 block029_data_flat147) := by decide +kernel
theorem block029_data_flat148_original : block029_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) := by
  rw [block029_data_flat148_step, block029_data_flat146_original, block029_data_flat147_original]
def block029_data_flat149 : CoefficientMerge.Poly := [(nat_lit 6613, Int.ofNat (nat_lit 6166081152000))]
theorem block029_data_flat149_step : block029_data_flat149 = (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) := by decide +kernel
theorem block029_data_flat149_original : block029_data_flat149 = (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) := by
  rw [block029_data_flat149_step]
def block029_data_flat150 : CoefficientMerge.Poly := [(nat_lit 6614, Int.ofNat (nat_lit 3083040576000))]
theorem block029_data_flat150_step : block029_data_flat150 = (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) := by decide +kernel
theorem block029_data_flat150_original : block029_data_flat150 = (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) := by
  rw [block029_data_flat150_step]
def block029_data_flat151 : CoefficientMerge.Poly := [(nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat151_step : block029_data_flat151 = (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded) := by decide +kernel
theorem block029_data_flat151_original : block029_data_flat151 = (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded) := by
  rw [block029_data_flat151_step]
def block029_data_flat152 : CoefficientMerge.Poly := [(nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat152_step : block029_data_flat152 = (CoefficientMerge.fastMerge block029_data_flat150 block029_data_flat151) := by decide +kernel
theorem block029_data_flat152_original : block029_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)) := by
  rw [block029_data_flat152_step, block029_data_flat150_original, block029_data_flat151_original]
def block029_data_flat153 : CoefficientMerge.Poly := [(nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat153_step : block029_data_flat153 = (CoefficientMerge.fastMerge block029_data_flat149 block029_data_flat152) := by decide +kernel
theorem block029_data_flat153_original : block029_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded))) := by
  rw [block029_data_flat153_step, block029_data_flat149_original, block029_data_flat152_original]
def block029_data_flat154 : CoefficientMerge.Poly := [(nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat154_step : block029_data_flat154 = (CoefficientMerge.fastMerge block029_data_flat148 block029_data_flat153) := by decide +kernel
theorem block029_data_flat154_original : block029_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)))) := by
  rw [block029_data_flat154_step, block029_data_flat148_original, block029_data_flat153_original]
def block029_data_flat155 : CoefficientMerge.Poly := [(nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat155_step : block029_data_flat155 = (CoefficientMerge.fastMerge block029_data_flat145 block029_data_flat154) := by decide +kernel
theorem block029_data_flat155_original : block029_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded))))) := by
  rw [block029_data_flat155_step, block029_data_flat145_original, block029_data_flat154_original]
def block029_data_flat156 : CoefficientMerge.Poly := [(nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088)), (nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat156_step : block029_data_flat156 = (CoefficientMerge.fastMerge block029_data_flat136 block029_data_flat155) := by decide +kernel
theorem block029_data_flat156_original : block029_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)))))) := by
  rw [block029_data_flat156_step, block029_data_flat136_original, block029_data_flat155_original]
def block029_data_flat157 : CoefficientMerge.Poly := [(nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700)), (nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544)), (nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088)), (nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat157_step : block029_data_flat157 = (CoefficientMerge.fastMerge block029_data_flat117 block029_data_flat156) := by decide +kernel
theorem block029_data_flat157_original : block029_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded))))))) := by
  rw [block029_data_flat157_step, block029_data_flat117_original, block029_data_flat156_original]
def block029_data_flat158 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200)), (nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272)), (nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872)), (nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280)), (nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700)), (nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544)), (nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088)), (nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat158_step : block029_data_flat158 = (CoefficientMerge.fastMerge block029_data_flat078 block029_data_flat157) := by decide +kernel
theorem block029_data_flat158_original : block029_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)))))))) := by
  rw [block029_data_flat158_step, block029_data_flat078_original, block029_data_flat157_original]
def block029_data_flat159 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6060, Int.ofNat (nat_lit 11171370949200)), (nat_lit 6061, Int.ofNat (nat_lit 15674337756000)), (nat_lit 6062, Int.ofNat (nat_lit 20819826165600)), (nat_lit 6063, Int.ofNat (nat_lit 25965314575200)), (nat_lit 6064, Int.ofNat (nat_lit 31110802984800)), (nat_lit 6065, Int.ofNat (nat_lit 36256291394400)), (nat_lit 6066, Int.ofNat (nat_lit 45334222105392)), (nat_lit 6068, Int.ofNat (nat_lit 62475180994512)), (nat_lit 6069, Int.ofNat (nat_lit 74122873486200)), (nat_lit 6070, Int.ofNat (nat_lit 153208246292640)), (nat_lit 6071, Int.ofNat (nat_lit 247986262408500)), (nat_lit 6085, Int.ofNat (nat_lit 27104843581200)), (nat_lit 6086, Int.ofNat (nat_lit 48070183946400)), (nat_lit 6087, Int.ofNat (nat_lit 51174486871200)), (nat_lit 6088, Int.ofNat (nat_lit 57361830372000)), (nat_lit 6089, Int.ofNat (nat_lit 63549173872800)), (nat_lit 6090, Int.ofNat (nat_lit 73075050903888)), (nat_lit 6091, Int.ofNat (nat_lit 42531469390080)), (nat_lit 6092, Int.ofNat (nat_lit 123990436996272)), (nat_lit 6093, Int.ofNat (nat_lit 139283462035080)), (nat_lit 6094, Int.ofNat (nat_lit 231954760353888)), (nat_lit 6095, Int.ofNat (nat_lit 339742267533900)), (nat_lit 6110, Int.ofNat (nat_lit 43567217139600)), (nat_lit 6111, Int.ofNat (nat_lit 85125142317600)), (nat_lit 6112, Int.ofNat (nat_lit 91333748167200)), (nat_lit 6113, Int.ofNat (nat_lit 97542354016800)), (nat_lit 6114, Int.ofNat (nat_lit 98659441119888)), (nat_lit 6115, Int.ofNat (nat_lit 89005622222880)), (nat_lit 6116, Int.ofNat (nat_lit 181911628693872)), (nat_lit 6117, Int.ofNat (nat_lit 210902114186280)), (nat_lit 6118, Int.ofNat (nat_lit 296892084189888)), (nat_lit 6119, Int.ofNat (nat_lit 409342572985500)), (nat_lit 6135, Int.ofNat (nat_lit 67242842528400)), (nat_lit 6136, Int.ofNat (nat_lit 126342205466400)), (nat_lit 6137, Int.ofNat (nat_lit 131551480922400)), (nat_lit 6138, Int.ofNat (nat_lit 146424341228688)), (nat_lit 6139, Int.ofNat (nat_lit 141191439828480)), (nat_lit 6140, Int.ofNat (nat_lit 276800336879472)), (nat_lit 6141, Int.ofNat (nat_lit 323185034474280)), (nat_lit 6142, Int.ofNat (nat_lit 355765957502688)), (nat_lit 6143, Int.ofNat (nat_lit 469518281927100)), (nat_lit 6160, Int.ofNat (nat_lit 87867320864400)), (nat_lit 6161, Int.ofNat (nat_lit 175840953472800)), (nat_lit 6162, Int.ofNat (nat_lit 176455475967888)), (nat_lit 6163, Int.ofNat (nat_lit 188873223482880)), (nat_lit 6164, Int.ofNat (nat_lit 342132769449072)), (nat_lit 6165, Int.ofNat (nat_lit 402956051584680)), (nat_lit 6166, Int.ofNat (nat_lit 392182562174688)), (nat_lit 6167, Int.ofNat (nat_lit 595302229928700)), (nat_lit 6185, Int.ofNat (nat_lit 111950474605200)), (nat_lit 6186, Int.ofNat (nat_lit 221385718393488)), (nat_lit 6187, Int.ofNat (nat_lit 256420484052480)), (nat_lit 6188, Int.ofNat (nat_lit 432297048162672)), (nat_lit 6189, Int.ofNat (nat_lit 510042099453480)), (nat_lit 6190, Int.ofNat (nat_lit 515066696280288)), (nat_lit 6191, Int.ofNat (nat_lit 732260508695100)), (nat_lit 6210, Int.ofNat (nat_lit 155797451099136)), (nat_lit 6211, Int.ofNat (nat_lit 337443300433008)), (nat_lit 6212, Int.ofNat (nat_lit 574554396344544)), (nat_lit 6213, Int.ofNat (nat_lit 618751227702168)), (nat_lit 6214, Int.ofNat (nat_lit 510055392621024)), (nat_lit 6215, Int.ofNat (nat_lit 755578774750140)), (nat_lit 6235, Int.ofNat (nat_lit 118417314212208)), (nat_lit 6236, Int.ofNat (nat_lit 457772204848464)), (nat_lit 6237, Int.ofNat (nat_lit 509935380181128)), (nat_lit 6238, Int.ofNat (nat_lit 417231228435936)), (nat_lit 6239, Int.ofNat (nat_lit 516076854392700)), (nat_lit 6260, Int.ofNat (nat_lit 346547254740192)), (nat_lit 6261, Int.ofNat (nat_lit 577171780724088)), (nat_lit 6262, Int.ofNat (nat_lit 437315251001568)), (nat_lit 6263, Int.ofNat (nat_lit 473142522455676)), (nat_lit 6285, Int.ofNat (nat_lit 169648736717592)), (nat_lit 6286, Int.ofNat (nat_lit 230976346924512)), (nat_lit 6287, Int.ofNat (nat_lit 260856825525180)), (nat_lit 6611, Int.ofNat (nat_lit 10703377792800)), (nat_lit 6612, Int.ofNat (nat_lit 9249121728000)), (nat_lit 6613, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6614, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6618, Int.ofNat (nat_lit 11628748118592))]
theorem block029_data_flat159_step : block029_data_flat159 = (CoefficientMerge.trim block029_data_flat158) := by decide +kernel
theorem block029_data_flat159_original : block029_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded))))))))) := by
  rw [block029_data_flat159_step, block029_data_flat158_original]
theorem block029_data : block029 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2129Coded) (CoefficientMerge.scale (11171370949200 : Int) atom2130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15674337756000 : Int) atom2131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20819826165600 : Int) atom2132Coded) (CoefficientMerge.scale (25965314575200 : Int) atom2133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31110802984800 : Int) atom2134Coded) (CoefficientMerge.scale (36256291394400 : Int) atom2135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45334222105392 : Int) atom2136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62475180994512 : Int) atom2137Coded) (CoefficientMerge.scale (74122873486200 : Int) atom2138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153208246292640 : Int) atom2139Coded) (CoefficientMerge.scale (247986262408500 : Int) atom2140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27104843581200 : Int) atom2141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48070183946400 : Int) atom2142Coded) (CoefficientMerge.scale (51174486871200 : Int) atom2143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57361830372000 : Int) atom2144Coded) (CoefficientMerge.scale (63549173872800 : Int) atom2145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73075050903888 : Int) atom2146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42531469390080 : Int) atom2147Coded) (CoefficientMerge.scale (123990436996272 : Int) atom2148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139283462035080 : Int) atom2149Coded) (CoefficientMerge.scale (231954760353888 : Int) atom2150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (339742267533900 : Int) atom2151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43567217139600 : Int) atom2152Coded) (CoefficientMerge.scale (85125142317600 : Int) atom2153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91333748167200 : Int) atom2154Coded) (CoefficientMerge.scale (97542354016800 : Int) atom2155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98659441119888 : Int) atom2156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89005622222880 : Int) atom2157Coded) (CoefficientMerge.scale (181911628693872 : Int) atom2158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210902114186280 : Int) atom2159Coded) (CoefficientMerge.scale (296892084189888 : Int) atom2160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409342572985500 : Int) atom2161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67242842528400 : Int) atom2162Coded) (CoefficientMerge.scale (126342205466400 : Int) atom2163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131551480922400 : Int) atom2164Coded) (CoefficientMerge.scale (146424341228688 : Int) atom2165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (141191439828480 : Int) atom2166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276800336879472 : Int) atom2167Coded) (CoefficientMerge.scale (323185034474280 : Int) atom2168Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355765957502688 : Int) atom2169Coded) (CoefficientMerge.scale (469518281927100 : Int) atom2170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87867320864400 : Int) atom2171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (175840953472800 : Int) atom2172Coded) (CoefficientMerge.scale (176455475967888 : Int) atom2173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (188873223482880 : Int) atom2174Coded) (CoefficientMerge.scale (342132769449072 : Int) atom2175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (402956051584680 : Int) atom2176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (392182562174688 : Int) atom2177Coded) (CoefficientMerge.scale (595302229928700 : Int) atom2178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111950474605200 : Int) atom2179Coded) (CoefficientMerge.scale (221385718393488 : Int) atom2180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256420484052480 : Int) atom2181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (432297048162672 : Int) atom2182Coded) (CoefficientMerge.scale (510042099453480 : Int) atom2183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (515066696280288 : Int) atom2184Coded) (CoefficientMerge.scale (732260508695100 : Int) atom2185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155797451099136 : Int) atom2186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (337443300433008 : Int) atom2187Coded) (CoefficientMerge.scale (574554396344544 : Int) atom2188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (618751227702168 : Int) atom2189Coded) (CoefficientMerge.scale (510055392621024 : Int) atom2190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (755578774750140 : Int) atom2191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118417314212208 : Int) atom2192Coded) (CoefficientMerge.scale (457772204848464 : Int) atom2193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (509935380181128 : Int) atom2194Coded) (CoefficientMerge.scale (417231228435936 : Int) atom2195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (516076854392700 : Int) atom2196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (346547254740192 : Int) atom2197Coded) (CoefficientMerge.scale (577171780724088 : Int) atom2198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437315251001568 : Int) atom2199Coded) (CoefficientMerge.scale (473142522455676 : Int) atom2200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169648736717592 : Int) atom2201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (230976346924512 : Int) atom2202Coded) (CoefficientMerge.scale (260856825525180 : Int) atom2203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10703377792800 : Int) atom2204Coded) (CoefficientMerge.scale (9249121728000 : Int) atom2205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2207Coded) (CoefficientMerge.scale (11628748118592 : Int) atom2208Coded)))))))) := by
  have h : block029 = block029_data_flat159 := by decide +kernel
  exact h.trans block029_data_flat159_original
theorem block029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block029 := by
  rw [block029_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2129Coded_nonneg g hg hA hB) (atom2130Coded_nonneg g hg hA hB)) (add_nonneg (atom2131Coded_nonneg g hg hA hB) (add_nonneg (atom2132Coded_nonneg g hg hA hB) (atom2133Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2134Coded_nonneg g hg hA hB) (atom2135Coded_nonneg g hg hA hB)) (add_nonneg (atom2136Coded_nonneg g hg hA hB) (add_nonneg (atom2137Coded_nonneg g hg hA hB) (atom2138Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2139Coded_nonneg g hg hA hB) (atom2140Coded_nonneg g hg hA hB)) (add_nonneg (atom2141Coded_nonneg g hg hA hB) (add_nonneg (atom2142Coded_nonneg g hg hA hB) (atom2143Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2144Coded_nonneg g hg hA hB) (atom2145Coded_nonneg g hg hA hB)) (add_nonneg (atom2146Coded_nonneg g hg hA hB) (add_nonneg (atom2147Coded_nonneg g hg hA hB) (atom2148Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2149Coded_nonneg g hg hA hB) (atom2150Coded_nonneg g hg hA hB)) (add_nonneg (atom2151Coded_nonneg g hg hA hB) (add_nonneg (atom2152Coded_nonneg g hg hA hB) (atom2153Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2154Coded_nonneg g hg hA hB) (atom2155Coded_nonneg g hg hA hB)) (add_nonneg (atom2156Coded_nonneg g hg hA hB) (add_nonneg (atom2157Coded_nonneg g hg hA hB) (atom2158Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2159Coded_nonneg g hg hA hB) (atom2160Coded_nonneg g hg hA hB)) (add_nonneg (atom2161Coded_nonneg g hg hA hB) (add_nonneg (atom2162Coded_nonneg g hg hA hB) (atom2163Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2164Coded_nonneg g hg hA hB) (atom2165Coded_nonneg g hg hA hB)) (add_nonneg (atom2166Coded_nonneg g hg hA hB) (add_nonneg (atom2167Coded_nonneg g hg hA hB) (atom2168Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2169Coded_nonneg g hg hA hB) (atom2170Coded_nonneg g hg hA hB)) (add_nonneg (atom2171Coded_nonneg g hg hA hB) (add_nonneg (atom2172Coded_nonneg g hg hA hB) (atom2173Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2174Coded_nonneg g hg hA hB) (atom2175Coded_nonneg g hg hA hB)) (add_nonneg (atom2176Coded_nonneg g hg hA hB) (add_nonneg (atom2177Coded_nonneg g hg hA hB) (atom2178Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2179Coded_nonneg g hg hA hB) (atom2180Coded_nonneg g hg hA hB)) (add_nonneg (atom2181Coded_nonneg g hg hA hB) (add_nonneg (atom2182Coded_nonneg g hg hA hB) (atom2183Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2184Coded_nonneg g hg hA hB) (atom2185Coded_nonneg g hg hA hB)) (add_nonneg (atom2186Coded_nonneg g hg hA hB) (add_nonneg (atom2187Coded_nonneg g hg hA hB) (atom2188Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2189Coded_nonneg g hg hA hB) (atom2190Coded_nonneg g hg hA hB)) (add_nonneg (atom2191Coded_nonneg g hg hA hB) (add_nonneg (atom2192Coded_nonneg g hg hA hB) (atom2193Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2194Coded_nonneg g hg hA hB) (atom2195Coded_nonneg g hg hA hB)) (add_nonneg (atom2196Coded_nonneg g hg hA hB) (add_nonneg (atom2197Coded_nonneg g hg hA hB) (atom2198Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2199Coded_nonneg g hg hA hB) (atom2200Coded_nonneg g hg hA hB)) (add_nonneg (atom2201Coded_nonneg g hg hA hB) (add_nonneg (atom2202Coded_nonneg g hg hA hB) (atom2203Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2204Coded_nonneg g hg hA hB) (atom2205Coded_nonneg g hg hA hB)) (add_nonneg (atom2206Coded_nonneg g hg hA hB) (add_nonneg (atom2207Coded_nonneg g hg hA hB) (atom2208Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
