import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2209 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom2209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2209 = ((g 11) * (g 12) * (g 12)) := by
  norm_num [atom2209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5906946276000 : Int) atom2209) := by
  rw [SparsePolynomial.eval_scale, eval_atom2209]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2209Coded : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 1))]
theorem atom2209Coded_decode : atom2209 = SparsePolynomial.decodeCubic 24 atom2209Coded := by decide +kernel
theorem atom2209Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) := by
  have h := atom2209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2210 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2210 = ((g 11) * (g 12) * (g 16)) := by
  norm_num [atom2210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2210) := by
  rw [SparsePolynomial.eval_scale, eval_atom2210]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2210Coded : CoefficientMerge.Poly := [(nat_lit 6640, Int.ofNat (nat_lit 1))]
theorem atom2210Coded_decode : atom2210 = SparsePolynomial.decodeCubic 24 atom2210Coded := by decide +kernel
theorem atom2210Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded) := by
  have h := atom2210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2211 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2211 = ((g 11) * (g 12) * (g 17)) := by
  norm_num [atom2211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2211) := by
  rw [SparsePolynomial.eval_scale, eval_atom2211]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2211Coded : CoefficientMerge.Poly := [(nat_lit 6641, Int.ofNat (nat_lit 1))]
theorem atom2211Coded_decode : atom2211 = SparsePolynomial.decodeCubic 24 atom2211Coded := by decide +kernel
theorem atom2211Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) := by
  have h := atom2211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2212 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2212 = ((g 11) * (g 12) * (g 18)) := by
  norm_num [atom2212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48198762938304 : Int) atom2212) := by
  rw [SparsePolynomial.eval_scale, eval_atom2212]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2212Coded : CoefficientMerge.Poly := [(nat_lit 6642, Int.ofNat (nat_lit 1))]
theorem atom2212Coded_decode : atom2212 = SparsePolynomial.decodeCubic 24 atom2212Coded := by decide +kernel
theorem atom2212Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) := by
  have h := atom2212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2213 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2213 = ((g 11) * (g 12) * (g 20)) := by
  norm_num [atom2213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55394670767040 : Int) atom2213) := by
  rw [SparsePolynomial.eval_scale, eval_atom2213]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2213Coded : CoefficientMerge.Poly := [(nat_lit 6644, Int.ofNat (nat_lit 1))]
theorem atom2213Coded_decode : atom2213 = SparsePolynomial.decodeCubic 24 atom2213Coded := by decide +kernel
theorem atom2213Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded) := by
  have h := atom2213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2214 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2214 = ((g 11) * (g 12) * (g 21)) := by
  norm_num [atom2214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48552573484800 : Int) atom2214) := by
  rw [SparsePolynomial.eval_scale, eval_atom2214]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2214Coded : CoefficientMerge.Poly := [(nat_lit 6645, Int.ofNat (nat_lit 1))]
theorem atom2214Coded_decode : atom2214 = SparsePolynomial.decodeCubic 24 atom2214Coded := by decide +kernel
theorem atom2214Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) := by
  have h := atom2214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2215 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2215 = ((g 11) * (g 12) * (g 22)) := by
  norm_num [atom2215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93303439004160 : Int) atom2215) := by
  rw [SparsePolynomial.eval_scale, eval_atom2215]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2215Coded : CoefficientMerge.Poly := [(nat_lit 6646, Int.ofNat (nat_lit 1))]
theorem atom2215Coded_decode : atom2215 = SparsePolynomial.decodeCubic 24 atom2215Coded := by decide +kernel
theorem atom2215Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded) := by
  have h := atom2215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2216 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2216 = ((g 11) * (g 12) * (g 23)) := by
  norm_num [atom2216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144759386217600 : Int) atom2216) := by
  rw [SparsePolynomial.eval_scale, eval_atom2216]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2216Coded : CoefficientMerge.Poly := [(nat_lit 6647, Int.ofNat (nat_lit 1))]
theorem atom2216Coded_decode : atom2216 = SparsePolynomial.decodeCubic 24 atom2216Coded := by decide +kernel
theorem atom2216Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) := by
  have h := atom2216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2217 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2217 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom2217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13611889922400 : Int) atom2217) := by
  rw [SparsePolynomial.eval_scale, eval_atom2217]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2217Coded : CoefficientMerge.Poly := [(nat_lit 6661, Int.ofNat (nat_lit 1))]
theorem atom2217Coded_decode : atom2217 = SparsePolynomial.decodeCubic 24 atom2217Coded := by decide +kernel
theorem atom2217Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) := by
  have h := atom2217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2218 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2218 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom2218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16959380961600 : Int) atom2218) := by
  rw [SparsePolynomial.eval_scale, eval_atom2218]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2218Coded : CoefficientMerge.Poly := [(nat_lit 6662, Int.ofNat (nat_lit 1))]
theorem atom2218Coded_decode : atom2218 = SparsePolynomial.decodeCubic 24 atom2218Coded := by decide +kernel
theorem atom2218Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded) := by
  have h := atom2218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2219 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2219 = ((g 11) * (g 13) * (g 15)) := by
  norm_num [atom2219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15938788219200 : Int) atom2219) := by
  rw [SparsePolynomial.eval_scale, eval_atom2219]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2219Coded : CoefficientMerge.Poly := [(nat_lit 6663, Int.ofNat (nat_lit 1))]
theorem atom2219Coded_decode : atom2219 = SparsePolynomial.decodeCubic 24 atom2219Coded := by decide +kernel
theorem atom2219Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) := by
  have h := atom2219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2220 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2220 = ((g 11) * (g 13) * (g 16)) := by
  norm_num [atom2220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21084276628800 : Int) atom2220) := by
  rw [SparsePolynomial.eval_scale, eval_atom2220]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2220Coded : CoefficientMerge.Poly := [(nat_lit 6664, Int.ofNat (nat_lit 1))]
theorem atom2220Coded_decode : atom2220 = SparsePolynomial.decodeCubic 24 atom2220Coded := by decide +kernel
theorem atom2220Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded) := by
  have h := atom2220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2221 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2221 = ((g 11) * (g 13) * (g 17)) := by
  norm_num [atom2221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26229765038400 : Int) atom2221) := by
  rw [SparsePolynomial.eval_scale, eval_atom2221]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2221Coded : CoefficientMerge.Poly := [(nat_lit 6665, Int.ofNat (nat_lit 1))]
theorem atom2221Coded_decode : atom2221 = SparsePolynomial.decodeCubic 24 atom2221Coded := by decide +kernel
theorem atom2221Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) := by
  have h := atom2221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2222 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2222 = ((g 11) * (g 13) * (g 18)) := by
  norm_num [atom2222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46202260100832 : Int) atom2222) := by
  rw [SparsePolynomial.eval_scale, eval_atom2222]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2222Coded : CoefficientMerge.Poly := [(nat_lit 6666, Int.ofNat (nat_lit 1))]
theorem atom2222Coded_decode : atom2222 = SparsePolynomial.decodeCubic 24 atom2222Coded := by decide +kernel
theorem atom2222Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) := by
  have h := atom2222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2223 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2223 = ((g 11) * (g 13) * (g 20)) := by
  norm_num [atom2223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81012310204320 : Int) atom2223) := by
  rw [SparsePolynomial.eval_scale, eval_atom2223]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2223Coded : CoefficientMerge.Poly := [(nat_lit 6668, Int.ofNat (nat_lit 1))]
theorem atom2223Coded_decode : atom2223 = SparsePolynomial.decodeCubic 24 atom2223Coded := by decide +kernel
theorem atom2223Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded) := by
  have h := atom2223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2224 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2224 = ((g 11) * (g 13) * (g 21)) := by
  norm_num [atom2224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81642768253200 : Int) atom2224) := by
  rw [SparsePolynomial.eval_scale, eval_atom2224]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2224Coded : CoefficientMerge.Poly := [(nat_lit 6669, Int.ofNat (nat_lit 1))]
theorem atom2224Coded_decode : atom2224 = SparsePolynomial.decodeCubic 24 atom2224Coded := by decide +kernel
theorem atom2224Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) := by
  have h := atom2224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2225 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2225 = ((g 11) * (g 13) * (g 22)) := by
  norm_num [atom2225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163234772648640 : Int) atom2225) := by
  rw [SparsePolynomial.eval_scale, eval_atom2225]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2225Coded : CoefficientMerge.Poly := [(nat_lit 6670, Int.ofNat (nat_lit 1))]
theorem atom2225Coded_decode : atom2225 = SparsePolynomial.decodeCubic 24 atom2225Coded := by decide +kernel
theorem atom2225Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded) := by
  have h := atom2225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2226 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2226 = ((g 11) * (g 13) * (g 23)) := by
  norm_num [atom2226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259266104559000 : Int) atom2226) := by
  rw [SparsePolynomial.eval_scale, eval_atom2226]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2226Coded : CoefficientMerge.Poly := [(nat_lit 6671, Int.ofNat (nat_lit 1))]
theorem atom2226Coded_decode : atom2226 = SparsePolynomial.decodeCubic 24 atom2226Coded := by decide +kernel
theorem atom2226Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) := by
  have h := atom2226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2227 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2227 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom2227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22866327237600 : Int) atom2227) := by
  rw [SparsePolynomial.eval_scale, eval_atom2227]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2227Coded : CoefficientMerge.Poly := [(nat_lit 6686, Int.ofNat (nat_lit 1))]
theorem atom2227Coded_decode : atom2227 = SparsePolynomial.decodeCubic 24 atom2227Coded := by decide +kernel
theorem atom2227Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) := by
  have h := atom2227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2228 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2228 = ((g 11) * (g 14) * (g 15)) := by
  norm_num [atom2228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40619059588800 : Int) atom2228) := by
  rw [SparsePolynomial.eval_scale, eval_atom2228]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2228Coded : CoefficientMerge.Poly := [(nat_lit 6687, Int.ofNat (nat_lit 1))]
theorem atom2228Coded_decode : atom2228 = SparsePolynomial.decodeCubic 24 atom2228Coded := by decide +kernel
theorem atom2228Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded) := by
  have h := atom2228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2229 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2229 = ((g 11) * (g 14) * (g 16)) := by
  norm_num [atom2229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46806403089600 : Int) atom2229) := by
  rw [SparsePolynomial.eval_scale, eval_atom2229]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2229Coded : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 1))]
theorem atom2229Coded_decode : atom2229 = SparsePolynomial.decodeCubic 24 atom2229Coded := by decide +kernel
theorem atom2229Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) := by
  have h := atom2229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2230 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2230 = ((g 11) * (g 14) * (g 17)) := by
  norm_num [atom2230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52993746590400 : Int) atom2230) := by
  rw [SparsePolynomial.eval_scale, eval_atom2230]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2230Coded : CoefficientMerge.Poly := [(nat_lit 6689, Int.ofNat (nat_lit 1))]
theorem atom2230Coded_decode : atom2230 = SparsePolynomial.decodeCubic 24 atom2230Coded := by decide +kernel
theorem atom2230Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded) := by
  have h := atom2230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2231 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2231 = ((g 11) * (g 14) * (g 18)) := by
  norm_num [atom2231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61134145671456 : Int) atom2231) := by
  rw [SparsePolynomial.eval_scale, eval_atom2231]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2231Coded : CoefficientMerge.Poly := [(nat_lit 6690, Int.ofNat (nat_lit 1))]
theorem atom2231Coded_decode : atom2231 = SparsePolynomial.decodeCubic 24 atom2231Coded := by decide +kernel
theorem atom2231Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) := by
  have h := atom2231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2232 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2232 = ((g 11) * (g 14) * (g 19)) := by
  norm_num [atom2232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35750728427040 : Int) atom2232) := by
  rw [SparsePolynomial.eval_scale, eval_atom2232]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2232Coded : CoefficientMerge.Poly := [(nat_lit 6691, Int.ofNat (nat_lit 1))]
theorem atom2232Coded_decode : atom2232 = SparsePolynomial.decodeCubic 24 atom2232Coded := by decide +kernel
theorem atom2232Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) := by
  have h := atom2232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2233 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2233 = ((g 11) * (g 14) * (g 20)) := by
  norm_num [atom2233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134843930321760 : Int) atom2233) := by
  rw [SparsePolynomial.eval_scale, eval_atom2233]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2233Coded : CoefficientMerge.Poly := [(nat_lit 6692, Int.ofNat (nat_lit 1))]
theorem atom2233Coded_decode : atom2233 = SparsePolynomial.decodeCubic 24 atom2233Coded := by decide +kernel
theorem atom2233Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded) := by
  have h := atom2233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2234 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2234 = ((g 11) * (g 14) * (g 21)) := by
  norm_num [atom2234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152999071608240 : Int) atom2234) := by
  rw [SparsePolynomial.eval_scale, eval_atom2234]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2234Coded : CoefficientMerge.Poly := [(nat_lit 6693, Int.ofNat (nat_lit 1))]
theorem atom2234Coded_decode : atom2234 = SparsePolynomial.decodeCubic 24 atom2234Coded := by decide +kernel
theorem atom2234Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) := by
  have h := atom2234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2235 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2235 = ((g 11) * (g 14) * (g 22)) := by
  norm_num [atom2235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238441743058464 : Int) atom2235) := by
  rw [SparsePolynomial.eval_scale, eval_atom2235]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2235Coded : CoefficientMerge.Poly := [(nat_lit 6694, Int.ofNat (nat_lit 1))]
theorem atom2235Coded_decode : atom2235 = SparsePolynomial.decodeCubic 24 atom2235Coded := by decide +kernel
theorem atom2235Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded) := by
  have h := atom2235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2236 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2236 = ((g 11) * (g 14) * (g 23)) := by
  norm_num [atom2236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351617123226600 : Int) atom2236) := by
  rw [SparsePolynomial.eval_scale, eval_atom2236]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2236Coded : CoefficientMerge.Poly := [(nat_lit 6695, Int.ofNat (nat_lit 1))]
theorem atom2236Coded_decode : atom2236 = SparsePolynomial.decodeCubic 24 atom2236Coded := by decide +kernel
theorem atom2236Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) := by
  have h := atom2236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2237 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2237 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom2237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40354609125600 : Int) atom2237) := by
  rw [SparsePolynomial.eval_scale, eval_atom2237]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2237Coded : CoefficientMerge.Poly := [(nat_lit 6711, Int.ofNat (nat_lit 1))]
theorem atom2237Coded_decode : atom2237 = SparsePolynomial.decodeCubic 24 atom2237Coded := by decide +kernel
theorem atom2237Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) := by
  have h := atom2237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2238 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2238 = ((g 11) * (g 15) * (g 16)) := by
  norm_num [atom2238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73565069054400 : Int) atom2238) := by
  rw [SparsePolynomial.eval_scale, eval_atom2238]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2238Coded : CoefficientMerge.Poly := [(nat_lit 6712, Int.ofNat (nat_lit 1))]
theorem atom2238Coded_decode : atom2238 = SparsePolynomial.decodeCubic 24 atom2238Coded := by decide +kernel
theorem atom2238Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded) := by
  have h := atom2238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2239 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2239 = ((g 11) * (g 15) * (g 17)) := by
  norm_num [atom2239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79773674904000 : Int) atom2239) := by
  rw [SparsePolynomial.eval_scale, eval_atom2239]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2239Coded : CoefficientMerge.Poly := [(nat_lit 6713, Int.ofNat (nat_lit 1))]
theorem atom2239Coded_decode : atom2239 = SparsePolynomial.decodeCubic 24 atom2239Coded := by decide +kernel
theorem atom2239Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) := by
  have h := atom2239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2240 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2240 = ((g 11) * (g 15) * (g 18)) := by
  norm_num [atom2240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108303700013856 : Int) atom2240) := by
  rw [SparsePolynomial.eval_scale, eval_atom2240]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2240Coded : CoefficientMerge.Poly := [(nat_lit 6714, Int.ofNat (nat_lit 1))]
theorem atom2240Coded_decode : atom2240 = SparsePolynomial.decodeCubic 24 atom2240Coded := by decide +kernel
theorem atom2240Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded) := by
  have h := atom2240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2241 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2241 = ((g 11) * (g 15) * (g 19)) := by
  norm_num [atom2241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93975053091840 : Int) atom2241) := by
  rw [SparsePolynomial.eval_scale, eval_atom2241]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2241Coded : CoefficientMerge.Poly := [(nat_lit 6715, Int.ofNat (nat_lit 1))]
theorem atom2241Coded_decode : atom2241 = SparsePolynomial.decodeCubic 24 atom2241Coded := by decide +kernel
theorem atom2241Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) := by
  have h := atom2241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2242 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2242 = ((g 11) * (g 15) * (g 20)) := by
  norm_num [atom2242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242404998392160 : Int) atom2242) := by
  rw [SparsePolynomial.eval_scale, eval_atom2242]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2242Coded : CoefficientMerge.Poly := [(nat_lit 6716, Int.ofNat (nat_lit 1))]
theorem atom2242Coded_decode : atom2242 = SparsePolynomial.decodeCubic 24 atom2242Coded := by decide +kernel
theorem atom2242Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) := by
  have h := atom2242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2243 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2243 = ((g 11) * (g 15) * (g 21)) := by
  norm_num [atom2243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (281781574565040 : Int) atom2243) := by
  rw [SparsePolynomial.eval_scale, eval_atom2243]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2243Coded : CoefficientMerge.Poly := [(nat_lit 6717, Int.ofNat (nat_lit 1))]
theorem atom2243Coded_decode : atom2243 = SparsePolynomial.decodeCubic 24 atom2243Coded := by decide +kernel
theorem atom2243Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded) := by
  have h := atom2243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2244 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2244 = ((g 11) * (g 15) * (g 22)) := by
  norm_num [atom2244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317642421824064 : Int) atom2244) := by
  rw [SparsePolynomial.eval_scale, eval_atom2244]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2244Coded : CoefficientMerge.Poly := [(nat_lit 6718, Int.ofNat (nat_lit 1))]
theorem atom2244Coded_decode : atom2244 = SparsePolynomial.decodeCubic 24 atom2244Coded := by decide +kernel
theorem atom2244Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) := by
  have h := atom2244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2245 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2245 = ((g 11) * (g 15) * (g 23)) := by
  norm_num [atom2245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434543545384200 : Int) atom2245) := by
  rw [SparsePolynomial.eval_scale, eval_atom2245]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2245Coded : CoefficientMerge.Poly := [(nat_lit 6719, Int.ofNat (nat_lit 1))]
theorem atom2245Coded_decode : atom2245 = SparsePolynomial.decodeCubic 24 atom2245Coded := by decide +kernel
theorem atom2245Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded) := by
  have h := atom2245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2246 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2246 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom2246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58895377279200 : Int) atom2246) := by
  rw [SparsePolynomial.eval_scale, eval_atom2246]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2246Coded : CoefficientMerge.Poly := [(nat_lit 6736, Int.ofNat (nat_lit 1))]
theorem atom2246Coded_decode : atom2246 = SparsePolynomial.decodeCubic 24 atom2246Coded := by decide +kernel
theorem atom2246Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) := by
  have h := atom2246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2247 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2247 = ((g 11) * (g 16) * (g 17)) := by
  norm_num [atom2247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119916989438400 : Int) atom2247) := by
  rw [SparsePolynomial.eval_scale, eval_atom2247]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2247Coded : CoefficientMerge.Poly := [(nat_lit 6737, Int.ofNat (nat_lit 1))]
theorem atom2247Coded_decode : atom2247 = SparsePolynomial.decodeCubic 24 atom2247Coded := by decide +kernel
theorem atom2247Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) := by
  have h := atom2247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2248 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2248 = ((g 11) * (g 16) * (g 18)) := by
  norm_num [atom2248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139281009274656 : Int) atom2248) := by
  rw [SparsePolynomial.eval_scale, eval_atom2248]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2248Coded : CoefficientMerge.Poly := [(nat_lit 6738, Int.ofNat (nat_lit 1))]
theorem atom2248Coded_decode : atom2248 = SparsePolynomial.decodeCubic 24 atom2248Coded := by decide +kernel
theorem atom2248Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded) := by
  have h := atom2248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2249 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2249 = ((g 11) * (g 16) * (g 19)) := by
  norm_num [atom2249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147695343805440 : Int) atom2249) := by
  rw [SparsePolynomial.eval_scale, eval_atom2249]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2249Coded : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 1))]
theorem atom2249Coded_decode : atom2249 = SparsePolynomial.decodeCubic 24 atom2249Coded := by decide +kernel
theorem atom2249Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) := by
  have h := atom2249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2250 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2250 = ((g 11) * (g 16) * (g 20)) := by
  norm_num [atom2250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318868270558560 : Int) atom2250) := by
  rw [SparsePolynomial.eval_scale, eval_atom2250]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2250Coded : CoefficientMerge.Poly := [(nat_lit 6740, Int.ofNat (nat_lit 1))]
theorem atom2250Coded_decode : atom2250 = SparsePolynomial.decodeCubic 24 atom2250Coded := by decide +kernel
theorem atom2250Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded) := by
  have h := atom2250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2251 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2251 = ((g 11) * (g 16) * (g 21)) := by
  norm_num [atom2251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375739893912240 : Int) atom2251) := by
  rw [SparsePolynomial.eval_scale, eval_atom2251]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2251Coded : CoefficientMerge.Poly := [(nat_lit 6741, Int.ofNat (nat_lit 1))]
theorem atom2251Coded_decode : atom2251 = SparsePolynomial.decodeCubic 24 atom2251Coded := by decide +kernel
theorem atom2251Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) := by
  have h := atom2251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2252 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2252 = ((g 11) * (g 16) * (g 22)) := by
  norm_num [atom2252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (371302791372864 : Int) atom2252) := by
  rw [SparsePolynomial.eval_scale, eval_atom2252]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2252Coded : CoefficientMerge.Poly := [(nat_lit 6742, Int.ofNat (nat_lit 1))]
theorem atom2252Coded_decode : atom2252 = SparsePolynomial.decodeCubic 24 atom2252Coded := by decide +kernel
theorem atom2252Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) := by
  have h := atom2252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2253 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2253 = ((g 11) * (g 16) * (g 23)) := by
  norm_num [atom2253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (579609785953800 : Int) atom2253) := by
  rw [SparsePolynomial.eval_scale, eval_atom2253]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2253Coded : CoefficientMerge.Poly := [(nat_lit 6743, Int.ofNat (nat_lit 1))]
theorem atom2253Coded_decode : atom2253 = SparsePolynomial.decodeCubic 24 atom2253Coded := by decide +kernel
theorem atom2253Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded) := by
  have h := atom2253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2254 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2254 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom2254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81915413580000 : Int) atom2254) := by
  rw [SparsePolynomial.eval_scale, eval_atom2254]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2254Coded : CoefficientMerge.Poly := [(nat_lit 6761, Int.ofNat (nat_lit 1))]
theorem atom2254Coded_decode : atom2254 = SparsePolynomial.decodeCubic 24 atom2254Coded := by decide +kernel
theorem atom2254Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) := by
  have h := atom2254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2255 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2255 = ((g 11) * (g 17) * (g 18)) := by
  norm_num [atom2255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185157426221856 : Int) atom2255) := by
  rw [SparsePolynomial.eval_scale, eval_atom2255]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2255Coded : CoefficientMerge.Poly := [(nat_lit 6762, Int.ofNat (nat_lit 1))]
theorem atom2255Coded_decode : atom2255 = SparsePolynomial.decodeCubic 24 atom2255Coded := by decide +kernel
theorem atom2255Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded) := by
  have h := atom2255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2256 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2256 = ((g 11) * (g 17) * (g 19)) := by
  norm_num [atom2256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221281111434240 : Int) atom2256) := by
  rw [SparsePolynomial.eval_scale, eval_atom2256]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2256Coded : CoefficientMerge.Poly := [(nat_lit 6763, Int.ofNat (nat_lit 1))]
theorem atom2256Coded_decode : atom2256 = SparsePolynomial.decodeCubic 24 atom2256Coded := by decide +kernel
theorem atom2256Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) := by
  have h := atom2256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2257 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2257 = ((g 11) * (g 17) * (g 20)) := by
  norm_num [atom2257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (420163388868960 : Int) atom2257) := by
  rw [SparsePolynomial.eval_scale, eval_atom2257]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2257Coded : CoefficientMerge.Poly := [(nat_lit 6764, Int.ofNat (nat_lit 1))]
theorem atom2257Coded_decode : atom2257 = SparsePolynomial.decodeCubic 24 atom2257Coded := by decide +kernel
theorem atom2257Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) := by
  have h := atom2257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2258 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2258 = ((g 11) * (g 17) * (g 21)) := by
  norm_num [atom2258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497013244017840 : Int) atom2258) := by
  rw [SparsePolynomial.eval_scale, eval_atom2258]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2258Coded : CoefficientMerge.Poly := [(nat_lit 6765, Int.ofNat (nat_lit 1))]
theorem atom2258Coded_decode : atom2258 = SparsePolynomial.decodeCubic 24 atom2258Coded := by decide +kernel
theorem atom2258Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded) := by
  have h := atom2258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2259 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2259 = ((g 11) * (g 17) * (g 22)) := by
  norm_num [atom2259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (511430690355264 : Int) atom2259) := by
  rw [SparsePolynomial.eval_scale, eval_atom2259]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2259Coded : CoefficientMerge.Poly := [(nat_lit 6766, Int.ofNat (nat_lit 1))]
theorem atom2259Coded_decode : atom2259 = SparsePolynomial.decodeCubic 24 atom2259Coded := by decide +kernel
theorem atom2259Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) := by
  have h := atom2259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2260 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2260 = ((g 11) * (g 17) * (g 23)) := by
  norm_num [atom2260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (735850357288200 : Int) atom2260) := by
  rw [SparsePolynomial.eval_scale, eval_atom2260]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2260Coded : CoefficientMerge.Poly := [(nat_lit 6767, Int.ofNat (nat_lit 1))]
theorem atom2260Coded_decode : atom2260 = SparsePolynomial.decodeCubic 24 atom2260Coded := by decide +kernel
theorem atom2260Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded) := by
  have h := atom2260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2261 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2261 = ((g 11) * (g 18) * (g 18)) := by
  norm_num [atom2261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144526252156704 : Int) atom2261) := by
  rw [SparsePolynomial.eval_scale, eval_atom2261]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2261Coded : CoefficientMerge.Poly := [(nat_lit 6786, Int.ofNat (nat_lit 1))]
theorem atom2261Coded_decode : atom2261 = SparsePolynomial.decodeCubic 24 atom2261Coded := by decide +kernel
theorem atom2261Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) := by
  have h := atom2261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2262 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2262 = ((g 11) * (g 18) * (g 19)) := by
  norm_num [atom2262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324397015566624 : Int) atom2262) := by
  rw [SparsePolynomial.eval_scale, eval_atom2262]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2262Coded : CoefficientMerge.Poly := [(nat_lit 6787, Int.ofNat (nat_lit 1))]
theorem atom2262Coded_decode : atom2262 = SparsePolynomial.decodeCubic 24 atom2262Coded := by decide +kernel
theorem atom2262Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) := by
  have h := atom2262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2263 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2263 = ((g 11) * (g 18) * (g 20)) := by
  norm_num [atom2263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (581962621382208 : Int) atom2263) := by
  rw [SparsePolynomial.eval_scale, eval_atom2263]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2263Coded : CoefficientMerge.Poly := [(nat_lit 6788, Int.ofNat (nat_lit 1))]
theorem atom2263Coded_decode : atom2263 = SparsePolynomial.decodeCubic 24 atom2263Coded := by decide +kernel
theorem atom2263Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded) := by
  have h := atom2263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2264 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2264 = ((g 11) * (g 18) * (g 21)) := by
  norm_num [atom2264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (633493976528160 : Int) atom2264) := by
  rw [SparsePolynomial.eval_scale, eval_atom2264]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2264Coded : CoefficientMerge.Poly := [(nat_lit 6789, Int.ofNat (nat_lit 1))]
theorem atom2264Coded_decode : atom2264 = SparsePolynomial.decodeCubic 24 atom2264Coded := by decide +kernel
theorem atom2264Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) := by
  have h := atom2264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2265 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2265 = ((g 11) * (g 18) * (g 22)) := by
  norm_num [atom2265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521271618266880 : Int) atom2265) := by
  rw [SparsePolynomial.eval_scale, eval_atom2265]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2265Coded : CoefficientMerge.Poly := [(nat_lit 6790, Int.ofNat (nat_lit 1))]
theorem atom2265Coded_decode : atom2265 = SparsePolynomial.decodeCubic 24 atom2265Coded := by decide +kernel
theorem atom2265Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded) := by
  have h := atom2265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2266 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2266 = ((g 11) * (g 18) * (g 23)) := by
  norm_num [atom2266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (777605283823104 : Int) atom2266) := by
  rw [SparsePolynomial.eval_scale, eval_atom2266]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2266Coded : CoefficientMerge.Poly := [(nat_lit 6791, Int.ofNat (nat_lit 1))]
theorem atom2266Coded_decode : atom2266 = SparsePolynomial.decodeCubic 24 atom2266Coded := by decide +kernel
theorem atom2266Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) := by
  have h := atom2266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2267 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2267 = ((g 11) * (g 19) * (g 19)) := by
  norm_num [atom2267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122940715654944 : Int) atom2267) := by
  rw [SparsePolynomial.eval_scale, eval_atom2267]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2267Coded : CoefficientMerge.Poly := [(nat_lit 6811, Int.ofNat (nat_lit 1))]
theorem atom2267Coded_decode : atom2267 = SparsePolynomial.decodeCubic 24 atom2267Coded := by decide +kernel
theorem atom2267Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) := by
  have h := atom2267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2268 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2268 = ((g 11) * (g 19) * (g 20)) := by
  norm_num [atom2268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (496098769380192 : Int) atom2268) := by
  rw [SparsePolynomial.eval_scale, eval_atom2268]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2268Coded : CoefficientMerge.Poly := [(nat_lit 6812, Int.ofNat (nat_lit 1))]
theorem atom2268Coded_decode : atom2268 = SparsePolynomial.decodeCubic 24 atom2268Coded := by decide +kernel
theorem atom2268Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded) := by
  have h := atom2268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2269 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2269 = ((g 11) * (g 19) * (g 21)) := by
  norm_num [atom2269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (569514416012784 : Int) atom2269) := by
  rw [SparsePolynomial.eval_scale, eval_atom2269]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2269Coded : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 1))]
theorem atom2269Coded_decode : atom2269 = SparsePolynomial.decodeCubic 24 atom2269Coded := by decide +kernel
theorem atom2269Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) := by
  have h := atom2269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2270 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2270 = ((g 11) * (g 19) * (g 22)) := by
  norm_num [atom2270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (438392507673408 : Int) atom2270) := by
  rw [SparsePolynomial.eval_scale, eval_atom2270]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2270Coded : CoefficientMerge.Poly := [(nat_lit 6814, Int.ofNat (nat_lit 1))]
theorem atom2270Coded_decode : atom2270 = SparsePolynomial.decodeCubic 24 atom2270Coded := by decide +kernel
theorem atom2270Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded) := by
  have h := atom2270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2271 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2271 = ((g 11) * (g 19) * (g 23)) := by
  norm_num [atom2271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (574036927094664 : Int) atom2271) := by
  rw [SparsePolynomial.eval_scale, eval_atom2271]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2271Coded : CoefficientMerge.Poly := [(nat_lit 6815, Int.ofNat (nat_lit 1))]
theorem atom2271Coded_decode : atom2271 = SparsePolynomial.decodeCubic 24 atom2271Coded := by decide +kernel
theorem atom2271Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) := by
  have h := atom2271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2272 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2272 = ((g 11) * (g 20) * (g 20)) := by
  norm_num [atom2272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375690508310304 : Int) atom2272) := by
  rw [SparsePolynomial.eval_scale, eval_atom2272]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2272Coded : CoefficientMerge.Poly := [(nat_lit 6836, Int.ofNat (nat_lit 1))]
theorem atom2272Coded_decode : atom2272 = SparsePolynomial.decodeCubic 24 atom2272Coded := by decide +kernel
theorem atom2272Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) := by
  have h := atom2272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2273 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2273 = ((g 11) * (g 20) * (g 21)) := by
  norm_num [atom2273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (665149508233056 : Int) atom2273) := by
  rw [SparsePolynomial.eval_scale, eval_atom2273]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2273Coded : CoefficientMerge.Poly := [(nat_lit 6837, Int.ofNat (nat_lit 1))]
theorem atom2273Coded_decode : atom2273 = SparsePolynomial.decodeCubic 24 atom2273Coded := by decide +kernel
theorem atom2273Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded) := by
  have h := atom2273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2274 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2274 = ((g 11) * (g 20) * (g 22)) := by
  norm_num [atom2274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (474164878364160 : Int) atom2274) := by
  rw [SparsePolynomial.eval_scale, eval_atom2274]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2274Coded : CoefficientMerge.Poly := [(nat_lit 6838, Int.ofNat (nat_lit 1))]
theorem atom2274Coded_decode : atom2274 = SparsePolynomial.decodeCubic 24 atom2274Coded := by decide +kernel
theorem atom2274Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) := by
  have h := atom2274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2275 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2275 = ((g 11) * (g 20) * (g 23)) := by
  norm_num [atom2275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (486459607582080 : Int) atom2275) := by
  rw [SparsePolynomial.eval_scale, eval_atom2275]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2275Coded : CoefficientMerge.Poly := [(nat_lit 6839, Int.ofNat (nat_lit 1))]
theorem atom2275Coded_decode : atom2275 = SparsePolynomial.decodeCubic 24 atom2275Coded := by decide +kernel
theorem atom2275Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded) := by
  have h := atom2275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2276 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2276 = ((g 11) * (g 21) * (g 21)) := by
  norm_num [atom2276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229503465479376 : Int) atom2276) := by
  rw [SparsePolynomial.eval_scale, eval_atom2276]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2276Coded : CoefficientMerge.Poly := [(nat_lit 6861, Int.ofNat (nat_lit 1))]
theorem atom2276Coded_decode : atom2276 = SparsePolynomial.decodeCubic 24 atom2276Coded := by decide +kernel
theorem atom2276Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) := by
  have h := atom2276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2277 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2277 = ((g 11) * (g 21) * (g 22)) := by
  norm_num [atom2277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284380297379136 : Int) atom2277) := by
  rw [SparsePolynomial.eval_scale, eval_atom2277]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 11) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2277Coded : CoefficientMerge.Poly := [(nat_lit 6862, Int.ofNat (nat_lit 1))]
theorem atom2277Coded_decode : atom2277 = SparsePolynomial.decodeCubic 24 atom2277Coded := by decide +kernel
theorem atom2277Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) := by
  have h := atom2277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2278 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2278 = ((g 11) * (g 21) * (g 23)) := by
  norm_num [atom2278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305111741840136 : Int) atom2278) := by
  rw [SparsePolynomial.eval_scale, eval_atom2278]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2278Coded : CoefficientMerge.Poly := [(nat_lit 6863, Int.ofNat (nat_lit 1))]
theorem atom2278Coded_decode : atom2278 = SparsePolynomial.decodeCubic 24 atom2278Coded := by decide +kernel
theorem atom2278Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded) := by
  have h := atom2278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2279 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2279 = ((g 11) * (g 22) * (g 23)) := by
  norm_num [atom2279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31657349589696 : Int) atom2279) := by
  rw [SparsePolynomial.eval_scale, eval_atom2279]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 11) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2279Coded : CoefficientMerge.Poly := [(nat_lit 6887, Int.ofNat (nat_lit 1))]
theorem atom2279Coded_decode : atom2279 = SparsePolynomial.decodeCubic 24 atom2279Coded := by decide +kernel
theorem atom2279Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) := by
  have h := atom2279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2280 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom2280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2280 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom2280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3937964184000 : Int) atom2280) := by
  rw [SparsePolynomial.eval_scale, eval_atom2280]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2280Coded : CoefficientMerge.Poly := [(nat_lit 7212, Int.ofNat (nat_lit 1))]
theorem atom2280Coded_decode : atom2280 = SparsePolynomial.decodeCubic 24 atom2280Coded := by decide +kernel
theorem atom2280Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded) := by
  have h := atom2280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2281 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2281 = ((g 12) * (g 12) * (g 18)) := by
  norm_num [atom2281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40371722785152 : Int) atom2281) := by
  rw [SparsePolynomial.eval_scale, eval_atom2281]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2281Coded : CoefficientMerge.Poly := [(nat_lit 7218, Int.ofNat (nat_lit 1))]
theorem atom2281Coded_decode : atom2281 = SparsePolynomial.decodeCubic 24 atom2281Coded := by decide +kernel
theorem atom2281Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) := by
  have h := atom2281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2282 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2282 = ((g 12) * (g 12) * (g 20)) := by
  norm_num [atom2282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44798908302720 : Int) atom2282) := by
  rw [SparsePolynomial.eval_scale, eval_atom2282]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2282Coded : CoefficientMerge.Poly := [(nat_lit 7220, Int.ofNat (nat_lit 1))]
theorem atom2282Coded_decode : atom2282 = SparsePolynomial.decodeCubic 24 atom2282Coded := by decide +kernel
theorem atom2282Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) := by
  have h := atom2282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2283 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2283 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom2283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4621903070400 : Int) atom2283) := by
  rw [SparsePolynomial.eval_scale, eval_atom2283]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2283Coded : CoefficientMerge.Poly := [(nat_lit 7237, Int.ofNat (nat_lit 1))]
theorem atom2283Coded_decode : atom2283 = SparsePolynomial.decodeCubic 24 atom2283Coded := by decide +kernel
theorem atom2283Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded) := by
  have h := atom2283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2284 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2284 = ((g 12) * (g 13) * (g 16)) := by
  norm_num [atom2284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2284) := by
  rw [SparsePolynomial.eval_scale, eval_atom2284]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2284Coded : CoefficientMerge.Poly := [(nat_lit 7240, Int.ofNat (nat_lit 1))]
theorem atom2284Coded_decode : atom2284 = SparsePolynomial.decodeCubic 24 atom2284Coded := by decide +kernel
theorem atom2284Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) := by
  have h := atom2284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2285 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2285 = ((g 12) * (g 13) * (g 17)) := by
  norm_num [atom2285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2285) := by
  rw [SparsePolynomial.eval_scale, eval_atom2285]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2285Coded : CoefficientMerge.Poly := [(nat_lit 7241, Int.ofNat (nat_lit 1))]
theorem atom2285Coded_decode : atom2285 = SparsePolynomial.decodeCubic 24 atom2285Coded := by decide +kernel
theorem atom2285Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded) := by
  have h := atom2285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2286 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2286 = ((g 12) * (g 13) * (g 18)) := by
  norm_num [atom2286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71194290659712 : Int) atom2286) := by
  rw [SparsePolynomial.eval_scale, eval_atom2286]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2286Coded : CoefficientMerge.Poly := [(nat_lit 7242, Int.ofNat (nat_lit 1))]
theorem atom2286Coded_decode : atom2286 = SparsePolynomial.decodeCubic 24 atom2286Coded := by decide +kernel
theorem atom2286Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) := by
  have h := atom2286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2287 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2287 = ((g 12) * (g 13) * (g 20)) := by
  norm_num [atom2287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125183510939520 : Int) atom2287) := by
  rw [SparsePolynomial.eval_scale, eval_atom2287]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2287Coded : CoefficientMerge.Poly := [(nat_lit 7244, Int.ofNat (nat_lit 1))]
theorem atom2287Coded_decode : atom2287 = SparsePolynomial.decodeCubic 24 atom2287Coded := by decide +kernel
theorem atom2287Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) := by
  have h := atom2287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2288 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2288 = ((g 12) * (g 13) * (g 21)) := by
  norm_num [atom2288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48552573484800 : Int) atom2288) := by
  rw [SparsePolynomial.eval_scale, eval_atom2288]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2288Coded : CoefficientMerge.Poly := [(nat_lit 7245, Int.ofNat (nat_lit 1))]
theorem atom2288Coded_decode : atom2288 = SparsePolynomial.decodeCubic 24 atom2288Coded := by decide +kernel
theorem atom2288Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded) := by
  have h := atom2288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block030 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600)), (nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800)), (nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400)), (nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656)), (nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840)), (nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192)), (nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136)), (nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data : block030 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)))))))) := by decide +kernel
theorem block030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block030 := by
  rw [block030_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2209Coded_nonneg g hg hA hB) (atom2210Coded_nonneg g hg hA hB)) (add_nonneg (atom2211Coded_nonneg g hg hA hB) (add_nonneg (atom2212Coded_nonneg g hg hA hB) (atom2213Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2214Coded_nonneg g hg hA hB) (atom2215Coded_nonneg g hg hA hB)) (add_nonneg (atom2216Coded_nonneg g hg hA hB) (add_nonneg (atom2217Coded_nonneg g hg hA hB) (atom2218Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2219Coded_nonneg g hg hA hB) (atom2220Coded_nonneg g hg hA hB)) (add_nonneg (atom2221Coded_nonneg g hg hA hB) (add_nonneg (atom2222Coded_nonneg g hg hA hB) (atom2223Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2224Coded_nonneg g hg hA hB) (atom2225Coded_nonneg g hg hA hB)) (add_nonneg (atom2226Coded_nonneg g hg hA hB) (add_nonneg (atom2227Coded_nonneg g hg hA hB) (atom2228Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2229Coded_nonneg g hg hA hB) (atom2230Coded_nonneg g hg hA hB)) (add_nonneg (atom2231Coded_nonneg g hg hA hB) (add_nonneg (atom2232Coded_nonneg g hg hA hB) (atom2233Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2234Coded_nonneg g hg hA hB) (atom2235Coded_nonneg g hg hA hB)) (add_nonneg (atom2236Coded_nonneg g hg hA hB) (add_nonneg (atom2237Coded_nonneg g hg hA hB) (atom2238Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2239Coded_nonneg g hg hA hB) (atom2240Coded_nonneg g hg hA hB)) (add_nonneg (atom2241Coded_nonneg g hg hA hB) (add_nonneg (atom2242Coded_nonneg g hg hA hB) (atom2243Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2244Coded_nonneg g hg hA hB) (atom2245Coded_nonneg g hg hA hB)) (add_nonneg (atom2246Coded_nonneg g hg hA hB) (add_nonneg (atom2247Coded_nonneg g hg hA hB) (atom2248Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2249Coded_nonneg g hg hA hB) (atom2250Coded_nonneg g hg hA hB)) (add_nonneg (atom2251Coded_nonneg g hg hA hB) (add_nonneg (atom2252Coded_nonneg g hg hA hB) (atom2253Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2254Coded_nonneg g hg hA hB) (atom2255Coded_nonneg g hg hA hB)) (add_nonneg (atom2256Coded_nonneg g hg hA hB) (add_nonneg (atom2257Coded_nonneg g hg hA hB) (atom2258Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2259Coded_nonneg g hg hA hB) (atom2260Coded_nonneg g hg hA hB)) (add_nonneg (atom2261Coded_nonneg g hg hA hB) (add_nonneg (atom2262Coded_nonneg g hg hA hB) (atom2263Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2264Coded_nonneg g hg hA hB) (atom2265Coded_nonneg g hg hA hB)) (add_nonneg (atom2266Coded_nonneg g hg hA hB) (add_nonneg (atom2267Coded_nonneg g hg hA hB) (atom2268Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2269Coded_nonneg g hg hA hB) (atom2270Coded_nonneg g hg hA hB)) (add_nonneg (atom2271Coded_nonneg g hg hA hB) (add_nonneg (atom2272Coded_nonneg g hg hA hB) (atom2273Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2274Coded_nonneg g hg hA hB) (atom2275Coded_nonneg g hg hA hB)) (add_nonneg (atom2276Coded_nonneg g hg hA hB) (add_nonneg (atom2277Coded_nonneg g hg hA hB) (atom2278Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2279Coded_nonneg g hg hA hB) (atom2280Coded_nonneg g hg hA hB)) (add_nonneg (atom2281Coded_nonneg g hg hA hB) (add_nonneg (atom2282Coded_nonneg g hg hA hB) (atom2283Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2284Coded_nonneg g hg hA hB) (atom2285Coded_nonneg g hg hA hB)) (add_nonneg (atom2286Coded_nonneg g hg hA hB) (add_nonneg (atom2287Coded_nonneg g hg hA hB) (atom2288Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
