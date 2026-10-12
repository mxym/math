-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
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
def block030_data_flat000 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000))]
theorem block030_data_flat000_step : block030_data_flat000 = (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) := by decide +kernel
theorem block030_data_flat000_original : block030_data_flat000 = (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) := by
  rw [block030_data_flat000_step]
def block030_data_flat001 : CoefficientMerge.Poly := [(nat_lit 6640, Int.ofNat (nat_lit 3083040576000))]
theorem block030_data_flat001_step : block030_data_flat001 = (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded) := by decide +kernel
theorem block030_data_flat001_original : block030_data_flat001 = (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded) := by
  rw [block030_data_flat001_step]
def block030_data_flat002 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000))]
theorem block030_data_flat002_step : block030_data_flat002 = (CoefficientMerge.fastMerge block030_data_flat000 block030_data_flat001) := by decide +kernel
theorem block030_data_flat002_original : block030_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) := by
  rw [block030_data_flat002_step, block030_data_flat000_original, block030_data_flat001_original]
def block030_data_flat003 : CoefficientMerge.Poly := [(nat_lit 6641, Int.ofNat (nat_lit 6166081152000))]
theorem block030_data_flat003_step : block030_data_flat003 = (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) := by decide +kernel
theorem block030_data_flat003_original : block030_data_flat003 = (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) := by
  rw [block030_data_flat003_step]
def block030_data_flat004 : CoefficientMerge.Poly := [(nat_lit 6642, Int.ofNat (nat_lit 48198762938304))]
theorem block030_data_flat004_step : block030_data_flat004 = (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) := by decide +kernel
theorem block030_data_flat004_original : block030_data_flat004 = (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) := by
  rw [block030_data_flat004_step]
def block030_data_flat005 : CoefficientMerge.Poly := [(nat_lit 6644, Int.ofNat (nat_lit 55394670767040))]
theorem block030_data_flat005_step : block030_data_flat005 = (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded) := by decide +kernel
theorem block030_data_flat005_original : block030_data_flat005 = (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded) := by
  rw [block030_data_flat005_step]
def block030_data_flat006 : CoefficientMerge.Poly := [(nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040))]
theorem block030_data_flat006_step : block030_data_flat006 = (CoefficientMerge.fastMerge block030_data_flat004 block030_data_flat005) := by decide +kernel
theorem block030_data_flat006_original : block030_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)) := by
  rw [block030_data_flat006_step, block030_data_flat004_original, block030_data_flat005_original]
def block030_data_flat007 : CoefficientMerge.Poly := [(nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040))]
theorem block030_data_flat007_step : block030_data_flat007 = (CoefficientMerge.fastMerge block030_data_flat003 block030_data_flat006) := by decide +kernel
theorem block030_data_flat007_original : block030_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded))) := by
  rw [block030_data_flat007_step, block030_data_flat003_original, block030_data_flat006_original]
def block030_data_flat008 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040))]
theorem block030_data_flat008_step : block030_data_flat008 = (CoefficientMerge.fastMerge block030_data_flat002 block030_data_flat007) := by decide +kernel
theorem block030_data_flat008_original : block030_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) := by
  rw [block030_data_flat008_step, block030_data_flat002_original, block030_data_flat007_original]
def block030_data_flat009 : CoefficientMerge.Poly := [(nat_lit 6645, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat009_step : block030_data_flat009 = (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) := by decide +kernel
theorem block030_data_flat009_original : block030_data_flat009 = (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) := by
  rw [block030_data_flat009_step]
def block030_data_flat010 : CoefficientMerge.Poly := [(nat_lit 6646, Int.ofNat (nat_lit 93303439004160))]
theorem block030_data_flat010_step : block030_data_flat010 = (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded) := by decide +kernel
theorem block030_data_flat010_original : block030_data_flat010 = (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded) := by
  rw [block030_data_flat010_step]
def block030_data_flat011 : CoefficientMerge.Poly := [(nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160))]
theorem block030_data_flat011_step : block030_data_flat011 = (CoefficientMerge.fastMerge block030_data_flat009 block030_data_flat010) := by decide +kernel
theorem block030_data_flat011_original : block030_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) := by
  rw [block030_data_flat011_step, block030_data_flat009_original, block030_data_flat010_original]
def block030_data_flat012 : CoefficientMerge.Poly := [(nat_lit 6647, Int.ofNat (nat_lit 144759386217600))]
theorem block030_data_flat012_step : block030_data_flat012 = (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) := by decide +kernel
theorem block030_data_flat012_original : block030_data_flat012 = (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) := by
  rw [block030_data_flat012_step]
def block030_data_flat013 : CoefficientMerge.Poly := [(nat_lit 6661, Int.ofNat (nat_lit 13611889922400))]
theorem block030_data_flat013_step : block030_data_flat013 = (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) := by decide +kernel
theorem block030_data_flat013_original : block030_data_flat013 = (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) := by
  rw [block030_data_flat013_step]
def block030_data_flat014 : CoefficientMerge.Poly := [(nat_lit 6662, Int.ofNat (nat_lit 16959380961600))]
theorem block030_data_flat014_step : block030_data_flat014 = (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded) := by decide +kernel
theorem block030_data_flat014_original : block030_data_flat014 = (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded) := by
  rw [block030_data_flat014_step]
def block030_data_flat015 : CoefficientMerge.Poly := [(nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600))]
theorem block030_data_flat015_step : block030_data_flat015 = (CoefficientMerge.fastMerge block030_data_flat013 block030_data_flat014) := by decide +kernel
theorem block030_data_flat015_original : block030_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded)) := by
  rw [block030_data_flat015_step, block030_data_flat013_original, block030_data_flat014_original]
def block030_data_flat016 : CoefficientMerge.Poly := [(nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600))]
theorem block030_data_flat016_step : block030_data_flat016 = (CoefficientMerge.fastMerge block030_data_flat012 block030_data_flat015) := by decide +kernel
theorem block030_data_flat016_original : block030_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))) := by
  rw [block030_data_flat016_step, block030_data_flat012_original, block030_data_flat015_original]
def block030_data_flat017 : CoefficientMerge.Poly := [(nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600))]
theorem block030_data_flat017_step : block030_data_flat017 = (CoefficientMerge.fastMerge block030_data_flat011 block030_data_flat016) := by decide +kernel
theorem block030_data_flat017_original : block030_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded)))) := by
  rw [block030_data_flat017_step, block030_data_flat011_original, block030_data_flat016_original]
def block030_data_flat018 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600))]
theorem block030_data_flat018_step : block030_data_flat018 = (CoefficientMerge.fastMerge block030_data_flat008 block030_data_flat017) := by decide +kernel
theorem block030_data_flat018_original : block030_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) := by
  rw [block030_data_flat018_step, block030_data_flat008_original, block030_data_flat017_original]
def block030_data_flat019 : CoefficientMerge.Poly := [(nat_lit 6663, Int.ofNat (nat_lit 15938788219200))]
theorem block030_data_flat019_step : block030_data_flat019 = (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) := by decide +kernel
theorem block030_data_flat019_original : block030_data_flat019 = (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) := by
  rw [block030_data_flat019_step]
def block030_data_flat020 : CoefficientMerge.Poly := [(nat_lit 6664, Int.ofNat (nat_lit 21084276628800))]
theorem block030_data_flat020_step : block030_data_flat020 = (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded) := by decide +kernel
theorem block030_data_flat020_original : block030_data_flat020 = (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded) := by
  rw [block030_data_flat020_step]
def block030_data_flat021 : CoefficientMerge.Poly := [(nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800))]
theorem block030_data_flat021_step : block030_data_flat021 = (CoefficientMerge.fastMerge block030_data_flat019 block030_data_flat020) := by decide +kernel
theorem block030_data_flat021_original : block030_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) := by
  rw [block030_data_flat021_step, block030_data_flat019_original, block030_data_flat020_original]
def block030_data_flat022 : CoefficientMerge.Poly := [(nat_lit 6665, Int.ofNat (nat_lit 26229765038400))]
theorem block030_data_flat022_step : block030_data_flat022 = (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) := by decide +kernel
theorem block030_data_flat022_original : block030_data_flat022 = (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) := by
  rw [block030_data_flat022_step]
def block030_data_flat023 : CoefficientMerge.Poly := [(nat_lit 6666, Int.ofNat (nat_lit 46202260100832))]
theorem block030_data_flat023_step : block030_data_flat023 = (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) := by decide +kernel
theorem block030_data_flat023_original : block030_data_flat023 = (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) := by
  rw [block030_data_flat023_step]
def block030_data_flat024 : CoefficientMerge.Poly := [(nat_lit 6668, Int.ofNat (nat_lit 81012310204320))]
theorem block030_data_flat024_step : block030_data_flat024 = (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded) := by decide +kernel
theorem block030_data_flat024_original : block030_data_flat024 = (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded) := by
  rw [block030_data_flat024_step]
def block030_data_flat025 : CoefficientMerge.Poly := [(nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320))]
theorem block030_data_flat025_step : block030_data_flat025 = (CoefficientMerge.fastMerge block030_data_flat023 block030_data_flat024) := by decide +kernel
theorem block030_data_flat025_original : block030_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)) := by
  rw [block030_data_flat025_step, block030_data_flat023_original, block030_data_flat024_original]
def block030_data_flat026 : CoefficientMerge.Poly := [(nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320))]
theorem block030_data_flat026_step : block030_data_flat026 = (CoefficientMerge.fastMerge block030_data_flat022 block030_data_flat025) := by decide +kernel
theorem block030_data_flat026_original : block030_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded))) := by
  rw [block030_data_flat026_step, block030_data_flat022_original, block030_data_flat025_original]
def block030_data_flat027 : CoefficientMerge.Poly := [(nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320))]
theorem block030_data_flat027_step : block030_data_flat027 = (CoefficientMerge.fastMerge block030_data_flat021 block030_data_flat026) := by decide +kernel
theorem block030_data_flat027_original : block030_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) := by
  rw [block030_data_flat027_step, block030_data_flat021_original, block030_data_flat026_original]
def block030_data_flat028 : CoefficientMerge.Poly := [(nat_lit 6669, Int.ofNat (nat_lit 81642768253200))]
theorem block030_data_flat028_step : block030_data_flat028 = (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) := by decide +kernel
theorem block030_data_flat028_original : block030_data_flat028 = (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) := by
  rw [block030_data_flat028_step]
def block030_data_flat029 : CoefficientMerge.Poly := [(nat_lit 6670, Int.ofNat (nat_lit 163234772648640))]
theorem block030_data_flat029_step : block030_data_flat029 = (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded) := by decide +kernel
theorem block030_data_flat029_original : block030_data_flat029 = (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded) := by
  rw [block030_data_flat029_step]
def block030_data_flat030 : CoefficientMerge.Poly := [(nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640))]
theorem block030_data_flat030_step : block030_data_flat030 = (CoefficientMerge.fastMerge block030_data_flat028 block030_data_flat029) := by decide +kernel
theorem block030_data_flat030_original : block030_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) := by
  rw [block030_data_flat030_step, block030_data_flat028_original, block030_data_flat029_original]
def block030_data_flat031 : CoefficientMerge.Poly := [(nat_lit 6671, Int.ofNat (nat_lit 259266104559000))]
theorem block030_data_flat031_step : block030_data_flat031 = (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) := by decide +kernel
theorem block030_data_flat031_original : block030_data_flat031 = (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) := by
  rw [block030_data_flat031_step]
def block030_data_flat032 : CoefficientMerge.Poly := [(nat_lit 6686, Int.ofNat (nat_lit 22866327237600))]
theorem block030_data_flat032_step : block030_data_flat032 = (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) := by decide +kernel
theorem block030_data_flat032_original : block030_data_flat032 = (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) := by
  rw [block030_data_flat032_step]
def block030_data_flat033 : CoefficientMerge.Poly := [(nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat033_step : block030_data_flat033 = (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded) := by decide +kernel
theorem block030_data_flat033_original : block030_data_flat033 = (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded) := by
  rw [block030_data_flat033_step]
def block030_data_flat034 : CoefficientMerge.Poly := [(nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat034_step : block030_data_flat034 = (CoefficientMerge.fastMerge block030_data_flat032 block030_data_flat033) := by decide +kernel
theorem block030_data_flat034_original : block030_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)) := by
  rw [block030_data_flat034_step, block030_data_flat032_original, block030_data_flat033_original]
def block030_data_flat035 : CoefficientMerge.Poly := [(nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat035_step : block030_data_flat035 = (CoefficientMerge.fastMerge block030_data_flat031 block030_data_flat034) := by decide +kernel
theorem block030_data_flat035_original : block030_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded))) := by
  rw [block030_data_flat035_step, block030_data_flat031_original, block030_data_flat034_original]
def block030_data_flat036 : CoefficientMerge.Poly := [(nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat036_step : block030_data_flat036 = (CoefficientMerge.fastMerge block030_data_flat030 block030_data_flat035) := by decide +kernel
theorem block030_data_flat036_original : block030_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))) := by
  rw [block030_data_flat036_step, block030_data_flat030_original, block030_data_flat035_original]
def block030_data_flat037 : CoefficientMerge.Poly := [(nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat037_step : block030_data_flat037 = (CoefficientMerge.fastMerge block030_data_flat027 block030_data_flat036) := by decide +kernel
theorem block030_data_flat037_original : block030_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded))))) := by
  rw [block030_data_flat037_step, block030_data_flat027_original, block030_data_flat036_original]
def block030_data_flat038 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600)), (nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800))]
theorem block030_data_flat038_step : block030_data_flat038 = (CoefficientMerge.fastMerge block030_data_flat018 block030_data_flat037) := by decide +kernel
theorem block030_data_flat038_original : block030_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) := by
  rw [block030_data_flat038_step, block030_data_flat018_original, block030_data_flat037_original]
def block030_data_flat039 : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 46806403089600))]
theorem block030_data_flat039_step : block030_data_flat039 = (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) := by decide +kernel
theorem block030_data_flat039_original : block030_data_flat039 = (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) := by
  rw [block030_data_flat039_step]
def block030_data_flat040 : CoefficientMerge.Poly := [(nat_lit 6689, Int.ofNat (nat_lit 52993746590400))]
theorem block030_data_flat040_step : block030_data_flat040 = (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded) := by decide +kernel
theorem block030_data_flat040_original : block030_data_flat040 = (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded) := by
  rw [block030_data_flat040_step]
def block030_data_flat041 : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400))]
theorem block030_data_flat041_step : block030_data_flat041 = (CoefficientMerge.fastMerge block030_data_flat039 block030_data_flat040) := by decide +kernel
theorem block030_data_flat041_original : block030_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) := by
  rw [block030_data_flat041_step, block030_data_flat039_original, block030_data_flat040_original]
def block030_data_flat042 : CoefficientMerge.Poly := [(nat_lit 6690, Int.ofNat (nat_lit 61134145671456))]
theorem block030_data_flat042_step : block030_data_flat042 = (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) := by decide +kernel
theorem block030_data_flat042_original : block030_data_flat042 = (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) := by
  rw [block030_data_flat042_step]
def block030_data_flat043 : CoefficientMerge.Poly := [(nat_lit 6691, Int.ofNat (nat_lit 35750728427040))]
theorem block030_data_flat043_step : block030_data_flat043 = (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) := by decide +kernel
theorem block030_data_flat043_original : block030_data_flat043 = (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) := by
  rw [block030_data_flat043_step]
def block030_data_flat044 : CoefficientMerge.Poly := [(nat_lit 6692, Int.ofNat (nat_lit 134843930321760))]
theorem block030_data_flat044_step : block030_data_flat044 = (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded) := by decide +kernel
theorem block030_data_flat044_original : block030_data_flat044 = (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded) := by
  rw [block030_data_flat044_step]
def block030_data_flat045 : CoefficientMerge.Poly := [(nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760))]
theorem block030_data_flat045_step : block030_data_flat045 = (CoefficientMerge.fastMerge block030_data_flat043 block030_data_flat044) := by decide +kernel
theorem block030_data_flat045_original : block030_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)) := by
  rw [block030_data_flat045_step, block030_data_flat043_original, block030_data_flat044_original]
def block030_data_flat046 : CoefficientMerge.Poly := [(nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760))]
theorem block030_data_flat046_step : block030_data_flat046 = (CoefficientMerge.fastMerge block030_data_flat042 block030_data_flat045) := by decide +kernel
theorem block030_data_flat046_original : block030_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded))) := by
  rw [block030_data_flat046_step, block030_data_flat042_original, block030_data_flat045_original]
def block030_data_flat047 : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760))]
theorem block030_data_flat047_step : block030_data_flat047 = (CoefficientMerge.fastMerge block030_data_flat041 block030_data_flat046) := by decide +kernel
theorem block030_data_flat047_original : block030_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) := by
  rw [block030_data_flat047_step, block030_data_flat041_original, block030_data_flat046_original]
def block030_data_flat048 : CoefficientMerge.Poly := [(nat_lit 6693, Int.ofNat (nat_lit 152999071608240))]
theorem block030_data_flat048_step : block030_data_flat048 = (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) := by decide +kernel
theorem block030_data_flat048_original : block030_data_flat048 = (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) := by
  rw [block030_data_flat048_step]
def block030_data_flat049 : CoefficientMerge.Poly := [(nat_lit 6694, Int.ofNat (nat_lit 238441743058464))]
theorem block030_data_flat049_step : block030_data_flat049 = (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded) := by decide +kernel
theorem block030_data_flat049_original : block030_data_flat049 = (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded) := by
  rw [block030_data_flat049_step]
def block030_data_flat050 : CoefficientMerge.Poly := [(nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464))]
theorem block030_data_flat050_step : block030_data_flat050 = (CoefficientMerge.fastMerge block030_data_flat048 block030_data_flat049) := by decide +kernel
theorem block030_data_flat050_original : block030_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) := by
  rw [block030_data_flat050_step, block030_data_flat048_original, block030_data_flat049_original]
def block030_data_flat051 : CoefficientMerge.Poly := [(nat_lit 6695, Int.ofNat (nat_lit 351617123226600))]
theorem block030_data_flat051_step : block030_data_flat051 = (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) := by decide +kernel
theorem block030_data_flat051_original : block030_data_flat051 = (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) := by
  rw [block030_data_flat051_step]
def block030_data_flat052 : CoefficientMerge.Poly := [(nat_lit 6711, Int.ofNat (nat_lit 40354609125600))]
theorem block030_data_flat052_step : block030_data_flat052 = (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) := by decide +kernel
theorem block030_data_flat052_original : block030_data_flat052 = (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) := by
  rw [block030_data_flat052_step]
def block030_data_flat053 : CoefficientMerge.Poly := [(nat_lit 6712, Int.ofNat (nat_lit 73565069054400))]
theorem block030_data_flat053_step : block030_data_flat053 = (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded) := by decide +kernel
theorem block030_data_flat053_original : block030_data_flat053 = (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded) := by
  rw [block030_data_flat053_step]
def block030_data_flat054 : CoefficientMerge.Poly := [(nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400))]
theorem block030_data_flat054_step : block030_data_flat054 = (CoefficientMerge.fastMerge block030_data_flat052 block030_data_flat053) := by decide +kernel
theorem block030_data_flat054_original : block030_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded)) := by
  rw [block030_data_flat054_step, block030_data_flat052_original, block030_data_flat053_original]
def block030_data_flat055 : CoefficientMerge.Poly := [(nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400))]
theorem block030_data_flat055_step : block030_data_flat055 = (CoefficientMerge.fastMerge block030_data_flat051 block030_data_flat054) := by decide +kernel
theorem block030_data_flat055_original : block030_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))) := by
  rw [block030_data_flat055_step, block030_data_flat051_original, block030_data_flat054_original]
def block030_data_flat056 : CoefficientMerge.Poly := [(nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400))]
theorem block030_data_flat056_step : block030_data_flat056 = (CoefficientMerge.fastMerge block030_data_flat050 block030_data_flat055) := by decide +kernel
theorem block030_data_flat056_original : block030_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded)))) := by
  rw [block030_data_flat056_step, block030_data_flat050_original, block030_data_flat055_original]
def block030_data_flat057 : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400))]
theorem block030_data_flat057_step : block030_data_flat057 = (CoefficientMerge.fastMerge block030_data_flat047 block030_data_flat056) := by decide +kernel
theorem block030_data_flat057_original : block030_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) := by
  rw [block030_data_flat057_step, block030_data_flat047_original, block030_data_flat056_original]
def block030_data_flat058 : CoefficientMerge.Poly := [(nat_lit 6713, Int.ofNat (nat_lit 79773674904000))]
theorem block030_data_flat058_step : block030_data_flat058 = (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) := by decide +kernel
theorem block030_data_flat058_original : block030_data_flat058 = (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) := by
  rw [block030_data_flat058_step]
def block030_data_flat059 : CoefficientMerge.Poly := [(nat_lit 6714, Int.ofNat (nat_lit 108303700013856))]
theorem block030_data_flat059_step : block030_data_flat059 = (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded) := by decide +kernel
theorem block030_data_flat059_original : block030_data_flat059 = (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded) := by
  rw [block030_data_flat059_step]
def block030_data_flat060 : CoefficientMerge.Poly := [(nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856))]
theorem block030_data_flat060_step : block030_data_flat060 = (CoefficientMerge.fastMerge block030_data_flat058 block030_data_flat059) := by decide +kernel
theorem block030_data_flat060_original : block030_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) := by
  rw [block030_data_flat060_step, block030_data_flat058_original, block030_data_flat059_original]
def block030_data_flat061 : CoefficientMerge.Poly := [(nat_lit 6715, Int.ofNat (nat_lit 93975053091840))]
theorem block030_data_flat061_step : block030_data_flat061 = (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) := by decide +kernel
theorem block030_data_flat061_original : block030_data_flat061 = (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) := by
  rw [block030_data_flat061_step]
def block030_data_flat062 : CoefficientMerge.Poly := [(nat_lit 6716, Int.ofNat (nat_lit 242404998392160))]
theorem block030_data_flat062_step : block030_data_flat062 = (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) := by decide +kernel
theorem block030_data_flat062_original : block030_data_flat062 = (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) := by
  rw [block030_data_flat062_step]
def block030_data_flat063 : CoefficientMerge.Poly := [(nat_lit 6717, Int.ofNat (nat_lit 281781574565040))]
theorem block030_data_flat063_step : block030_data_flat063 = (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded) := by decide +kernel
theorem block030_data_flat063_original : block030_data_flat063 = (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded) := by
  rw [block030_data_flat063_step]
def block030_data_flat064 : CoefficientMerge.Poly := [(nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040))]
theorem block030_data_flat064_step : block030_data_flat064 = (CoefficientMerge.fastMerge block030_data_flat062 block030_data_flat063) := by decide +kernel
theorem block030_data_flat064_original : block030_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)) := by
  rw [block030_data_flat064_step, block030_data_flat062_original, block030_data_flat063_original]
def block030_data_flat065 : CoefficientMerge.Poly := [(nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040))]
theorem block030_data_flat065_step : block030_data_flat065 = (CoefficientMerge.fastMerge block030_data_flat061 block030_data_flat064) := by decide +kernel
theorem block030_data_flat065_original : block030_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded))) := by
  rw [block030_data_flat065_step, block030_data_flat061_original, block030_data_flat064_original]
def block030_data_flat066 : CoefficientMerge.Poly := [(nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040))]
theorem block030_data_flat066_step : block030_data_flat066 = (CoefficientMerge.fastMerge block030_data_flat060 block030_data_flat065) := by decide +kernel
theorem block030_data_flat066_original : block030_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) := by
  rw [block030_data_flat066_step, block030_data_flat060_original, block030_data_flat065_original]
def block030_data_flat067 : CoefficientMerge.Poly := [(nat_lit 6718, Int.ofNat (nat_lit 317642421824064))]
theorem block030_data_flat067_step : block030_data_flat067 = (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) := by decide +kernel
theorem block030_data_flat067_original : block030_data_flat067 = (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) := by
  rw [block030_data_flat067_step]
def block030_data_flat068 : CoefficientMerge.Poly := [(nat_lit 6719, Int.ofNat (nat_lit 434543545384200))]
theorem block030_data_flat068_step : block030_data_flat068 = (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded) := by decide +kernel
theorem block030_data_flat068_original : block030_data_flat068 = (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded) := by
  rw [block030_data_flat068_step]
def block030_data_flat069 : CoefficientMerge.Poly := [(nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200))]
theorem block030_data_flat069_step : block030_data_flat069 = (CoefficientMerge.fastMerge block030_data_flat067 block030_data_flat068) := by decide +kernel
theorem block030_data_flat069_original : block030_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) := by
  rw [block030_data_flat069_step, block030_data_flat067_original, block030_data_flat068_original]
def block030_data_flat070 : CoefficientMerge.Poly := [(nat_lit 6736, Int.ofNat (nat_lit 58895377279200))]
theorem block030_data_flat070_step : block030_data_flat070 = (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) := by decide +kernel
theorem block030_data_flat070_original : block030_data_flat070 = (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) := by
  rw [block030_data_flat070_step]
def block030_data_flat071 : CoefficientMerge.Poly := [(nat_lit 6737, Int.ofNat (nat_lit 119916989438400))]
theorem block030_data_flat071_step : block030_data_flat071 = (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) := by decide +kernel
theorem block030_data_flat071_original : block030_data_flat071 = (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) := by
  rw [block030_data_flat071_step]
def block030_data_flat072 : CoefficientMerge.Poly := [(nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat072_step : block030_data_flat072 = (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded) := by decide +kernel
theorem block030_data_flat072_original : block030_data_flat072 = (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded) := by
  rw [block030_data_flat072_step]
def block030_data_flat073 : CoefficientMerge.Poly := [(nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat073_step : block030_data_flat073 = (CoefficientMerge.fastMerge block030_data_flat071 block030_data_flat072) := by decide +kernel
theorem block030_data_flat073_original : block030_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded)) := by
  rw [block030_data_flat073_step, block030_data_flat071_original, block030_data_flat072_original]
def block030_data_flat074 : CoefficientMerge.Poly := [(nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat074_step : block030_data_flat074 = (CoefficientMerge.fastMerge block030_data_flat070 block030_data_flat073) := by decide +kernel
theorem block030_data_flat074_original : block030_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))) := by
  rw [block030_data_flat074_step, block030_data_flat070_original, block030_data_flat073_original]
def block030_data_flat075 : CoefficientMerge.Poly := [(nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat075_step : block030_data_flat075 = (CoefficientMerge.fastMerge block030_data_flat069 block030_data_flat074) := by decide +kernel
theorem block030_data_flat075_original : block030_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded)))) := by
  rw [block030_data_flat075_step, block030_data_flat069_original, block030_data_flat074_original]
def block030_data_flat076 : CoefficientMerge.Poly := [(nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat076_step : block030_data_flat076 = (CoefficientMerge.fastMerge block030_data_flat066 block030_data_flat075) := by decide +kernel
theorem block030_data_flat076_original : block030_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))) := by
  rw [block030_data_flat076_step, block030_data_flat066_original, block030_data_flat075_original]
def block030_data_flat077 : CoefficientMerge.Poly := [(nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400)), (nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat077_step : block030_data_flat077 = (CoefficientMerge.fastMerge block030_data_flat057 block030_data_flat076) := by decide +kernel
theorem block030_data_flat077_original : block030_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded)))))) := by
  rw [block030_data_flat077_step, block030_data_flat057_original, block030_data_flat076_original]
def block030_data_flat078 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600)), (nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800)), (nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400)), (nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656))]
theorem block030_data_flat078_step : block030_data_flat078 = (CoefficientMerge.fastMerge block030_data_flat038 block030_data_flat077) := by decide +kernel
theorem block030_data_flat078_original : block030_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))))) := by
  rw [block030_data_flat078_step, block030_data_flat038_original, block030_data_flat077_original]
def block030_data_flat079 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440))]
theorem block030_data_flat079_step : block030_data_flat079 = (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) := by decide +kernel
theorem block030_data_flat079_original : block030_data_flat079 = (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) := by
  rw [block030_data_flat079_step]
def block030_data_flat080 : CoefficientMerge.Poly := [(nat_lit 6740, Int.ofNat (nat_lit 318868270558560))]
theorem block030_data_flat080_step : block030_data_flat080 = (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded) := by decide +kernel
theorem block030_data_flat080_original : block030_data_flat080 = (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded) := by
  rw [block030_data_flat080_step]
def block030_data_flat081 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560))]
theorem block030_data_flat081_step : block030_data_flat081 = (CoefficientMerge.fastMerge block030_data_flat079 block030_data_flat080) := by decide +kernel
theorem block030_data_flat081_original : block030_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) := by
  rw [block030_data_flat081_step, block030_data_flat079_original, block030_data_flat080_original]
def block030_data_flat082 : CoefficientMerge.Poly := [(nat_lit 6741, Int.ofNat (nat_lit 375739893912240))]
theorem block030_data_flat082_step : block030_data_flat082 = (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) := by decide +kernel
theorem block030_data_flat082_original : block030_data_flat082 = (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) := by
  rw [block030_data_flat082_step]
def block030_data_flat083 : CoefficientMerge.Poly := [(nat_lit 6742, Int.ofNat (nat_lit 371302791372864))]
theorem block030_data_flat083_step : block030_data_flat083 = (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) := by decide +kernel
theorem block030_data_flat083_original : block030_data_flat083 = (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) := by
  rw [block030_data_flat083_step]
def block030_data_flat084 : CoefficientMerge.Poly := [(nat_lit 6743, Int.ofNat (nat_lit 579609785953800))]
theorem block030_data_flat084_step : block030_data_flat084 = (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded) := by decide +kernel
theorem block030_data_flat084_original : block030_data_flat084 = (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded) := by
  rw [block030_data_flat084_step]
def block030_data_flat085 : CoefficientMerge.Poly := [(nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800))]
theorem block030_data_flat085_step : block030_data_flat085 = (CoefficientMerge.fastMerge block030_data_flat083 block030_data_flat084) := by decide +kernel
theorem block030_data_flat085_original : block030_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)) := by
  rw [block030_data_flat085_step, block030_data_flat083_original, block030_data_flat084_original]
def block030_data_flat086 : CoefficientMerge.Poly := [(nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800))]
theorem block030_data_flat086_step : block030_data_flat086 = (CoefficientMerge.fastMerge block030_data_flat082 block030_data_flat085) := by decide +kernel
theorem block030_data_flat086_original : block030_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded))) := by
  rw [block030_data_flat086_step, block030_data_flat082_original, block030_data_flat085_original]
def block030_data_flat087 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800))]
theorem block030_data_flat087_step : block030_data_flat087 = (CoefficientMerge.fastMerge block030_data_flat081 block030_data_flat086) := by decide +kernel
theorem block030_data_flat087_original : block030_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) := by
  rw [block030_data_flat087_step, block030_data_flat081_original, block030_data_flat086_original]
def block030_data_flat088 : CoefficientMerge.Poly := [(nat_lit 6761, Int.ofNat (nat_lit 81915413580000))]
theorem block030_data_flat088_step : block030_data_flat088 = (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) := by decide +kernel
theorem block030_data_flat088_original : block030_data_flat088 = (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) := by
  rw [block030_data_flat088_step]
def block030_data_flat089 : CoefficientMerge.Poly := [(nat_lit 6762, Int.ofNat (nat_lit 185157426221856))]
theorem block030_data_flat089_step : block030_data_flat089 = (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded) := by decide +kernel
theorem block030_data_flat089_original : block030_data_flat089 = (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded) := by
  rw [block030_data_flat089_step]
def block030_data_flat090 : CoefficientMerge.Poly := [(nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856))]
theorem block030_data_flat090_step : block030_data_flat090 = (CoefficientMerge.fastMerge block030_data_flat088 block030_data_flat089) := by decide +kernel
theorem block030_data_flat090_original : block030_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) := by
  rw [block030_data_flat090_step, block030_data_flat088_original, block030_data_flat089_original]
def block030_data_flat091 : CoefficientMerge.Poly := [(nat_lit 6763, Int.ofNat (nat_lit 221281111434240))]
theorem block030_data_flat091_step : block030_data_flat091 = (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) := by decide +kernel
theorem block030_data_flat091_original : block030_data_flat091 = (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) := by
  rw [block030_data_flat091_step]
def block030_data_flat092 : CoefficientMerge.Poly := [(nat_lit 6764, Int.ofNat (nat_lit 420163388868960))]
theorem block030_data_flat092_step : block030_data_flat092 = (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) := by decide +kernel
theorem block030_data_flat092_original : block030_data_flat092 = (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) := by
  rw [block030_data_flat092_step]
def block030_data_flat093 : CoefficientMerge.Poly := [(nat_lit 6765, Int.ofNat (nat_lit 497013244017840))]
theorem block030_data_flat093_step : block030_data_flat093 = (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded) := by decide +kernel
theorem block030_data_flat093_original : block030_data_flat093 = (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded) := by
  rw [block030_data_flat093_step]
def block030_data_flat094 : CoefficientMerge.Poly := [(nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840))]
theorem block030_data_flat094_step : block030_data_flat094 = (CoefficientMerge.fastMerge block030_data_flat092 block030_data_flat093) := by decide +kernel
theorem block030_data_flat094_original : block030_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded)) := by
  rw [block030_data_flat094_step, block030_data_flat092_original, block030_data_flat093_original]
def block030_data_flat095 : CoefficientMerge.Poly := [(nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840))]
theorem block030_data_flat095_step : block030_data_flat095 = (CoefficientMerge.fastMerge block030_data_flat091 block030_data_flat094) := by decide +kernel
theorem block030_data_flat095_original : block030_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))) := by
  rw [block030_data_flat095_step, block030_data_flat091_original, block030_data_flat094_original]
def block030_data_flat096 : CoefficientMerge.Poly := [(nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840))]
theorem block030_data_flat096_step : block030_data_flat096 = (CoefficientMerge.fastMerge block030_data_flat090 block030_data_flat095) := by decide +kernel
theorem block030_data_flat096_original : block030_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded)))) := by
  rw [block030_data_flat096_step, block030_data_flat090_original, block030_data_flat095_original]
def block030_data_flat097 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840))]
theorem block030_data_flat097_step : block030_data_flat097 = (CoefficientMerge.fastMerge block030_data_flat087 block030_data_flat096) := by decide +kernel
theorem block030_data_flat097_original : block030_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) := by
  rw [block030_data_flat097_step, block030_data_flat087_original, block030_data_flat096_original]
def block030_data_flat098 : CoefficientMerge.Poly := [(nat_lit 6766, Int.ofNat (nat_lit 511430690355264))]
theorem block030_data_flat098_step : block030_data_flat098 = (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) := by decide +kernel
theorem block030_data_flat098_original : block030_data_flat098 = (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) := by
  rw [block030_data_flat098_step]
def block030_data_flat099 : CoefficientMerge.Poly := [(nat_lit 6767, Int.ofNat (nat_lit 735850357288200))]
theorem block030_data_flat099_step : block030_data_flat099 = (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded) := by decide +kernel
theorem block030_data_flat099_original : block030_data_flat099 = (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded) := by
  rw [block030_data_flat099_step]
def block030_data_flat100 : CoefficientMerge.Poly := [(nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200))]
theorem block030_data_flat100_step : block030_data_flat100 = (CoefficientMerge.fastMerge block030_data_flat098 block030_data_flat099) := by decide +kernel
theorem block030_data_flat100_original : block030_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) := by
  rw [block030_data_flat100_step, block030_data_flat098_original, block030_data_flat099_original]
def block030_data_flat101 : CoefficientMerge.Poly := [(nat_lit 6786, Int.ofNat (nat_lit 144526252156704))]
theorem block030_data_flat101_step : block030_data_flat101 = (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) := by decide +kernel
theorem block030_data_flat101_original : block030_data_flat101 = (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) := by
  rw [block030_data_flat101_step]
def block030_data_flat102 : CoefficientMerge.Poly := [(nat_lit 6787, Int.ofNat (nat_lit 324397015566624))]
theorem block030_data_flat102_step : block030_data_flat102 = (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) := by decide +kernel
theorem block030_data_flat102_original : block030_data_flat102 = (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) := by
  rw [block030_data_flat102_step]
def block030_data_flat103 : CoefficientMerge.Poly := [(nat_lit 6788, Int.ofNat (nat_lit 581962621382208))]
theorem block030_data_flat103_step : block030_data_flat103 = (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded) := by decide +kernel
theorem block030_data_flat103_original : block030_data_flat103 = (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded) := by
  rw [block030_data_flat103_step]
def block030_data_flat104 : CoefficientMerge.Poly := [(nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208))]
theorem block030_data_flat104_step : block030_data_flat104 = (CoefficientMerge.fastMerge block030_data_flat102 block030_data_flat103) := by decide +kernel
theorem block030_data_flat104_original : block030_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)) := by
  rw [block030_data_flat104_step, block030_data_flat102_original, block030_data_flat103_original]
def block030_data_flat105 : CoefficientMerge.Poly := [(nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208))]
theorem block030_data_flat105_step : block030_data_flat105 = (CoefficientMerge.fastMerge block030_data_flat101 block030_data_flat104) := by decide +kernel
theorem block030_data_flat105_original : block030_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded))) := by
  rw [block030_data_flat105_step, block030_data_flat101_original, block030_data_flat104_original]
def block030_data_flat106 : CoefficientMerge.Poly := [(nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208))]
theorem block030_data_flat106_step : block030_data_flat106 = (CoefficientMerge.fastMerge block030_data_flat100 block030_data_flat105) := by decide +kernel
theorem block030_data_flat106_original : block030_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) := by
  rw [block030_data_flat106_step, block030_data_flat100_original, block030_data_flat105_original]
def block030_data_flat107 : CoefficientMerge.Poly := [(nat_lit 6789, Int.ofNat (nat_lit 633493976528160))]
theorem block030_data_flat107_step : block030_data_flat107 = (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) := by decide +kernel
theorem block030_data_flat107_original : block030_data_flat107 = (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) := by
  rw [block030_data_flat107_step]
def block030_data_flat108 : CoefficientMerge.Poly := [(nat_lit 6790, Int.ofNat (nat_lit 521271618266880))]
theorem block030_data_flat108_step : block030_data_flat108 = (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded) := by decide +kernel
theorem block030_data_flat108_original : block030_data_flat108 = (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded) := by
  rw [block030_data_flat108_step]
def block030_data_flat109 : CoefficientMerge.Poly := [(nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880))]
theorem block030_data_flat109_step : block030_data_flat109 = (CoefficientMerge.fastMerge block030_data_flat107 block030_data_flat108) := by decide +kernel
theorem block030_data_flat109_original : block030_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) := by
  rw [block030_data_flat109_step, block030_data_flat107_original, block030_data_flat108_original]
def block030_data_flat110 : CoefficientMerge.Poly := [(nat_lit 6791, Int.ofNat (nat_lit 777605283823104))]
theorem block030_data_flat110_step : block030_data_flat110 = (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) := by decide +kernel
theorem block030_data_flat110_original : block030_data_flat110 = (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) := by
  rw [block030_data_flat110_step]
def block030_data_flat111 : CoefficientMerge.Poly := [(nat_lit 6811, Int.ofNat (nat_lit 122940715654944))]
theorem block030_data_flat111_step : block030_data_flat111 = (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) := by decide +kernel
theorem block030_data_flat111_original : block030_data_flat111 = (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) := by
  rw [block030_data_flat111_step]
def block030_data_flat112 : CoefficientMerge.Poly := [(nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat112_step : block030_data_flat112 = (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded) := by decide +kernel
theorem block030_data_flat112_original : block030_data_flat112 = (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded) := by
  rw [block030_data_flat112_step]
def block030_data_flat113 : CoefficientMerge.Poly := [(nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat113_step : block030_data_flat113 = (CoefficientMerge.fastMerge block030_data_flat111 block030_data_flat112) := by decide +kernel
theorem block030_data_flat113_original : block030_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)) := by
  rw [block030_data_flat113_step, block030_data_flat111_original, block030_data_flat112_original]
def block030_data_flat114 : CoefficientMerge.Poly := [(nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat114_step : block030_data_flat114 = (CoefficientMerge.fastMerge block030_data_flat110 block030_data_flat113) := by decide +kernel
theorem block030_data_flat114_original : block030_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded))) := by
  rw [block030_data_flat114_step, block030_data_flat110_original, block030_data_flat113_original]
def block030_data_flat115 : CoefficientMerge.Poly := [(nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat115_step : block030_data_flat115 = (CoefficientMerge.fastMerge block030_data_flat109 block030_data_flat114) := by decide +kernel
theorem block030_data_flat115_original : block030_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))) := by
  rw [block030_data_flat115_step, block030_data_flat109_original, block030_data_flat114_original]
def block030_data_flat116 : CoefficientMerge.Poly := [(nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat116_step : block030_data_flat116 = (CoefficientMerge.fastMerge block030_data_flat106 block030_data_flat115) := by decide +kernel
theorem block030_data_flat116_original : block030_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded))))) := by
  rw [block030_data_flat116_step, block030_data_flat106_original, block030_data_flat115_original]
def block030_data_flat117 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840)), (nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192))]
theorem block030_data_flat117_step : block030_data_flat117 = (CoefficientMerge.fastMerge block030_data_flat097 block030_data_flat116) := by decide +kernel
theorem block030_data_flat117_original : block030_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) := by
  rw [block030_data_flat117_step, block030_data_flat097_original, block030_data_flat116_original]
def block030_data_flat118 : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 569514416012784))]
theorem block030_data_flat118_step : block030_data_flat118 = (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) := by decide +kernel
theorem block030_data_flat118_original : block030_data_flat118 = (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) := by
  rw [block030_data_flat118_step]
def block030_data_flat119 : CoefficientMerge.Poly := [(nat_lit 6814, Int.ofNat (nat_lit 438392507673408))]
theorem block030_data_flat119_step : block030_data_flat119 = (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded) := by decide +kernel
theorem block030_data_flat119_original : block030_data_flat119 = (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded) := by
  rw [block030_data_flat119_step]
def block030_data_flat120 : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408))]
theorem block030_data_flat120_step : block030_data_flat120 = (CoefficientMerge.fastMerge block030_data_flat118 block030_data_flat119) := by decide +kernel
theorem block030_data_flat120_original : block030_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) := by
  rw [block030_data_flat120_step, block030_data_flat118_original, block030_data_flat119_original]
def block030_data_flat121 : CoefficientMerge.Poly := [(nat_lit 6815, Int.ofNat (nat_lit 574036927094664))]
theorem block030_data_flat121_step : block030_data_flat121 = (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) := by decide +kernel
theorem block030_data_flat121_original : block030_data_flat121 = (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) := by
  rw [block030_data_flat121_step]
def block030_data_flat122 : CoefficientMerge.Poly := [(nat_lit 6836, Int.ofNat (nat_lit 375690508310304))]
theorem block030_data_flat122_step : block030_data_flat122 = (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) := by decide +kernel
theorem block030_data_flat122_original : block030_data_flat122 = (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) := by
  rw [block030_data_flat122_step]
def block030_data_flat123 : CoefficientMerge.Poly := [(nat_lit 6837, Int.ofNat (nat_lit 665149508233056))]
theorem block030_data_flat123_step : block030_data_flat123 = (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded) := by decide +kernel
theorem block030_data_flat123_original : block030_data_flat123 = (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded) := by
  rw [block030_data_flat123_step]
def block030_data_flat124 : CoefficientMerge.Poly := [(nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056))]
theorem block030_data_flat124_step : block030_data_flat124 = (CoefficientMerge.fastMerge block030_data_flat122 block030_data_flat123) := by decide +kernel
theorem block030_data_flat124_original : block030_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)) := by
  rw [block030_data_flat124_step, block030_data_flat122_original, block030_data_flat123_original]
def block030_data_flat125 : CoefficientMerge.Poly := [(nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056))]
theorem block030_data_flat125_step : block030_data_flat125 = (CoefficientMerge.fastMerge block030_data_flat121 block030_data_flat124) := by decide +kernel
theorem block030_data_flat125_original : block030_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded))) := by
  rw [block030_data_flat125_step, block030_data_flat121_original, block030_data_flat124_original]
def block030_data_flat126 : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056))]
theorem block030_data_flat126_step : block030_data_flat126 = (CoefficientMerge.fastMerge block030_data_flat120 block030_data_flat125) := by decide +kernel
theorem block030_data_flat126_original : block030_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) := by
  rw [block030_data_flat126_step, block030_data_flat120_original, block030_data_flat125_original]
def block030_data_flat127 : CoefficientMerge.Poly := [(nat_lit 6838, Int.ofNat (nat_lit 474164878364160))]
theorem block030_data_flat127_step : block030_data_flat127 = (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) := by decide +kernel
theorem block030_data_flat127_original : block030_data_flat127 = (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) := by
  rw [block030_data_flat127_step]
def block030_data_flat128 : CoefficientMerge.Poly := [(nat_lit 6839, Int.ofNat (nat_lit 486459607582080))]
theorem block030_data_flat128_step : block030_data_flat128 = (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded) := by decide +kernel
theorem block030_data_flat128_original : block030_data_flat128 = (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded) := by
  rw [block030_data_flat128_step]
def block030_data_flat129 : CoefficientMerge.Poly := [(nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080))]
theorem block030_data_flat129_step : block030_data_flat129 = (CoefficientMerge.fastMerge block030_data_flat127 block030_data_flat128) := by decide +kernel
theorem block030_data_flat129_original : block030_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) := by
  rw [block030_data_flat129_step, block030_data_flat127_original, block030_data_flat128_original]
def block030_data_flat130 : CoefficientMerge.Poly := [(nat_lit 6861, Int.ofNat (nat_lit 229503465479376))]
theorem block030_data_flat130_step : block030_data_flat130 = (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) := by decide +kernel
theorem block030_data_flat130_original : block030_data_flat130 = (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) := by
  rw [block030_data_flat130_step]
def block030_data_flat131 : CoefficientMerge.Poly := [(nat_lit 6862, Int.ofNat (nat_lit 284380297379136))]
theorem block030_data_flat131_step : block030_data_flat131 = (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) := by decide +kernel
theorem block030_data_flat131_original : block030_data_flat131 = (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) := by
  rw [block030_data_flat131_step]
def block030_data_flat132 : CoefficientMerge.Poly := [(nat_lit 6863, Int.ofNat (nat_lit 305111741840136))]
theorem block030_data_flat132_step : block030_data_flat132 = (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded) := by decide +kernel
theorem block030_data_flat132_original : block030_data_flat132 = (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded) := by
  rw [block030_data_flat132_step]
def block030_data_flat133 : CoefficientMerge.Poly := [(nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136))]
theorem block030_data_flat133_step : block030_data_flat133 = (CoefficientMerge.fastMerge block030_data_flat131 block030_data_flat132) := by decide +kernel
theorem block030_data_flat133_original : block030_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded)) := by
  rw [block030_data_flat133_step, block030_data_flat131_original, block030_data_flat132_original]
def block030_data_flat134 : CoefficientMerge.Poly := [(nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136))]
theorem block030_data_flat134_step : block030_data_flat134 = (CoefficientMerge.fastMerge block030_data_flat130 block030_data_flat133) := by decide +kernel
theorem block030_data_flat134_original : block030_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))) := by
  rw [block030_data_flat134_step, block030_data_flat130_original, block030_data_flat133_original]
def block030_data_flat135 : CoefficientMerge.Poly := [(nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136))]
theorem block030_data_flat135_step : block030_data_flat135 = (CoefficientMerge.fastMerge block030_data_flat129 block030_data_flat134) := by decide +kernel
theorem block030_data_flat135_original : block030_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded)))) := by
  rw [block030_data_flat135_step, block030_data_flat129_original, block030_data_flat134_original]
def block030_data_flat136 : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136))]
theorem block030_data_flat136_step : block030_data_flat136 = (CoefficientMerge.fastMerge block030_data_flat126 block030_data_flat135) := by decide +kernel
theorem block030_data_flat136_original : block030_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) := by
  rw [block030_data_flat136_step, block030_data_flat126_original, block030_data_flat135_original]
def block030_data_flat137 : CoefficientMerge.Poly := [(nat_lit 6887, Int.ofNat (nat_lit 31657349589696))]
theorem block030_data_flat137_step : block030_data_flat137 = (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) := by decide +kernel
theorem block030_data_flat137_original : block030_data_flat137 = (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) := by
  rw [block030_data_flat137_step]
def block030_data_flat138 : CoefficientMerge.Poly := [(nat_lit 7212, Int.ofNat (nat_lit 3937964184000))]
theorem block030_data_flat138_step : block030_data_flat138 = (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded) := by decide +kernel
theorem block030_data_flat138_original : block030_data_flat138 = (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded) := by
  rw [block030_data_flat138_step]
def block030_data_flat139 : CoefficientMerge.Poly := [(nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000))]
theorem block030_data_flat139_step : block030_data_flat139 = (CoefficientMerge.fastMerge block030_data_flat137 block030_data_flat138) := by decide +kernel
theorem block030_data_flat139_original : block030_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) := by
  rw [block030_data_flat139_step, block030_data_flat137_original, block030_data_flat138_original]
def block030_data_flat140 : CoefficientMerge.Poly := [(nat_lit 7218, Int.ofNat (nat_lit 40371722785152))]
theorem block030_data_flat140_step : block030_data_flat140 = (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) := by decide +kernel
theorem block030_data_flat140_original : block030_data_flat140 = (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) := by
  rw [block030_data_flat140_step]
def block030_data_flat141 : CoefficientMerge.Poly := [(nat_lit 7220, Int.ofNat (nat_lit 44798908302720))]
theorem block030_data_flat141_step : block030_data_flat141 = (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) := by decide +kernel
theorem block030_data_flat141_original : block030_data_flat141 = (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) := by
  rw [block030_data_flat141_step]
def block030_data_flat142 : CoefficientMerge.Poly := [(nat_lit 7237, Int.ofNat (nat_lit 4621903070400))]
theorem block030_data_flat142_step : block030_data_flat142 = (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded) := by decide +kernel
theorem block030_data_flat142_original : block030_data_flat142 = (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded) := by
  rw [block030_data_flat142_step]
def block030_data_flat143 : CoefficientMerge.Poly := [(nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400))]
theorem block030_data_flat143_step : block030_data_flat143 = (CoefficientMerge.fastMerge block030_data_flat141 block030_data_flat142) := by decide +kernel
theorem block030_data_flat143_original : block030_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)) := by
  rw [block030_data_flat143_step, block030_data_flat141_original, block030_data_flat142_original]
def block030_data_flat144 : CoefficientMerge.Poly := [(nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400))]
theorem block030_data_flat144_step : block030_data_flat144 = (CoefficientMerge.fastMerge block030_data_flat140 block030_data_flat143) := by decide +kernel
theorem block030_data_flat144_original : block030_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded))) := by
  rw [block030_data_flat144_step, block030_data_flat140_original, block030_data_flat143_original]
def block030_data_flat145 : CoefficientMerge.Poly := [(nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400))]
theorem block030_data_flat145_step : block030_data_flat145 = (CoefficientMerge.fastMerge block030_data_flat139 block030_data_flat144) := by decide +kernel
theorem block030_data_flat145_original : block030_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) := by
  rw [block030_data_flat145_step, block030_data_flat139_original, block030_data_flat144_original]
def block030_data_flat146 : CoefficientMerge.Poly := [(nat_lit 7240, Int.ofNat (nat_lit 3083040576000))]
theorem block030_data_flat146_step : block030_data_flat146 = (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) := by decide +kernel
theorem block030_data_flat146_original : block030_data_flat146 = (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) := by
  rw [block030_data_flat146_step]
def block030_data_flat147 : CoefficientMerge.Poly := [(nat_lit 7241, Int.ofNat (nat_lit 6166081152000))]
theorem block030_data_flat147_step : block030_data_flat147 = (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded) := by decide +kernel
theorem block030_data_flat147_original : block030_data_flat147 = (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded) := by
  rw [block030_data_flat147_step]
def block030_data_flat148 : CoefficientMerge.Poly := [(nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000))]
theorem block030_data_flat148_step : block030_data_flat148 = (CoefficientMerge.fastMerge block030_data_flat146 block030_data_flat147) := by decide +kernel
theorem block030_data_flat148_original : block030_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) := by
  rw [block030_data_flat148_step, block030_data_flat146_original, block030_data_flat147_original]
def block030_data_flat149 : CoefficientMerge.Poly := [(nat_lit 7242, Int.ofNat (nat_lit 71194290659712))]
theorem block030_data_flat149_step : block030_data_flat149 = (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) := by decide +kernel
theorem block030_data_flat149_original : block030_data_flat149 = (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) := by
  rw [block030_data_flat149_step]
def block030_data_flat150 : CoefficientMerge.Poly := [(nat_lit 7244, Int.ofNat (nat_lit 125183510939520))]
theorem block030_data_flat150_step : block030_data_flat150 = (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) := by decide +kernel
theorem block030_data_flat150_original : block030_data_flat150 = (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) := by
  rw [block030_data_flat150_step]
def block030_data_flat151 : CoefficientMerge.Poly := [(nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat151_step : block030_data_flat151 = (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded) := by decide +kernel
theorem block030_data_flat151_original : block030_data_flat151 = (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded) := by
  rw [block030_data_flat151_step]
def block030_data_flat152 : CoefficientMerge.Poly := [(nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat152_step : block030_data_flat152 = (CoefficientMerge.fastMerge block030_data_flat150 block030_data_flat151) := by decide +kernel
theorem block030_data_flat152_original : block030_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)) := by
  rw [block030_data_flat152_step, block030_data_flat150_original, block030_data_flat151_original]
def block030_data_flat153 : CoefficientMerge.Poly := [(nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat153_step : block030_data_flat153 = (CoefficientMerge.fastMerge block030_data_flat149 block030_data_flat152) := by decide +kernel
theorem block030_data_flat153_original : block030_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded))) := by
  rw [block030_data_flat153_step, block030_data_flat149_original, block030_data_flat152_original]
def block030_data_flat154 : CoefficientMerge.Poly := [(nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat154_step : block030_data_flat154 = (CoefficientMerge.fastMerge block030_data_flat148 block030_data_flat153) := by decide +kernel
theorem block030_data_flat154_original : block030_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)))) := by
  rw [block030_data_flat154_step, block030_data_flat148_original, block030_data_flat153_original]
def block030_data_flat155 : CoefficientMerge.Poly := [(nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat155_step : block030_data_flat155 = (CoefficientMerge.fastMerge block030_data_flat145 block030_data_flat154) := by decide +kernel
theorem block030_data_flat155_original : block030_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded))))) := by
  rw [block030_data_flat155_step, block030_data_flat145_original, block030_data_flat154_original]
def block030_data_flat156 : CoefficientMerge.Poly := [(nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136)), (nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat156_step : block030_data_flat156 = (CoefficientMerge.fastMerge block030_data_flat136 block030_data_flat155) := by decide +kernel
theorem block030_data_flat156_original : block030_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)))))) := by
  rw [block030_data_flat156_step, block030_data_flat136_original, block030_data_flat155_original]
def block030_data_flat157 : CoefficientMerge.Poly := [(nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840)), (nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192)), (nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136)), (nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat157_step : block030_data_flat157 = (CoefficientMerge.fastMerge block030_data_flat117 block030_data_flat156) := by decide +kernel
theorem block030_data_flat157_original : block030_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded))))))) := by
  rw [block030_data_flat157_step, block030_data_flat117_original, block030_data_flat156_original]
def block030_data_flat158 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600)), (nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800)), (nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400)), (nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656)), (nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840)), (nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192)), (nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136)), (nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat158_step : block030_data_flat158 = (CoefficientMerge.fastMerge block030_data_flat078 block030_data_flat157) := by decide +kernel
theorem block030_data_flat158_original : block030_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)))))))) := by
  rw [block030_data_flat158_step, block030_data_flat078_original, block030_data_flat157_original]
def block030_data_flat159 : CoefficientMerge.Poly := [(nat_lit 6636, Int.ofNat (nat_lit 5906946276000)), (nat_lit 6640, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6641, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6642, Int.ofNat (nat_lit 48198762938304)), (nat_lit 6644, Int.ofNat (nat_lit 55394670767040)), (nat_lit 6645, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6646, Int.ofNat (nat_lit 93303439004160)), (nat_lit 6647, Int.ofNat (nat_lit 144759386217600)), (nat_lit 6661, Int.ofNat (nat_lit 13611889922400)), (nat_lit 6662, Int.ofNat (nat_lit 16959380961600)), (nat_lit 6663, Int.ofNat (nat_lit 15938788219200)), (nat_lit 6664, Int.ofNat (nat_lit 21084276628800)), (nat_lit 6665, Int.ofNat (nat_lit 26229765038400)), (nat_lit 6666, Int.ofNat (nat_lit 46202260100832)), (nat_lit 6668, Int.ofNat (nat_lit 81012310204320)), (nat_lit 6669, Int.ofNat (nat_lit 81642768253200)), (nat_lit 6670, Int.ofNat (nat_lit 163234772648640)), (nat_lit 6671, Int.ofNat (nat_lit 259266104559000)), (nat_lit 6686, Int.ofNat (nat_lit 22866327237600)), (nat_lit 6687, Int.ofNat (nat_lit 40619059588800)), (nat_lit 6688, Int.ofNat (nat_lit 46806403089600)), (nat_lit 6689, Int.ofNat (nat_lit 52993746590400)), (nat_lit 6690, Int.ofNat (nat_lit 61134145671456)), (nat_lit 6691, Int.ofNat (nat_lit 35750728427040)), (nat_lit 6692, Int.ofNat (nat_lit 134843930321760)), (nat_lit 6693, Int.ofNat (nat_lit 152999071608240)), (nat_lit 6694, Int.ofNat (nat_lit 238441743058464)), (nat_lit 6695, Int.ofNat (nat_lit 351617123226600)), (nat_lit 6711, Int.ofNat (nat_lit 40354609125600)), (nat_lit 6712, Int.ofNat (nat_lit 73565069054400)), (nat_lit 6713, Int.ofNat (nat_lit 79773674904000)), (nat_lit 6714, Int.ofNat (nat_lit 108303700013856)), (nat_lit 6715, Int.ofNat (nat_lit 93975053091840)), (nat_lit 6716, Int.ofNat (nat_lit 242404998392160)), (nat_lit 6717, Int.ofNat (nat_lit 281781574565040)), (nat_lit 6718, Int.ofNat (nat_lit 317642421824064)), (nat_lit 6719, Int.ofNat (nat_lit 434543545384200)), (nat_lit 6736, Int.ofNat (nat_lit 58895377279200)), (nat_lit 6737, Int.ofNat (nat_lit 119916989438400)), (nat_lit 6738, Int.ofNat (nat_lit 139281009274656)), (nat_lit 6739, Int.ofNat (nat_lit 147695343805440)), (nat_lit 6740, Int.ofNat (nat_lit 318868270558560)), (nat_lit 6741, Int.ofNat (nat_lit 375739893912240)), (nat_lit 6742, Int.ofNat (nat_lit 371302791372864)), (nat_lit 6743, Int.ofNat (nat_lit 579609785953800)), (nat_lit 6761, Int.ofNat (nat_lit 81915413580000)), (nat_lit 6762, Int.ofNat (nat_lit 185157426221856)), (nat_lit 6763, Int.ofNat (nat_lit 221281111434240)), (nat_lit 6764, Int.ofNat (nat_lit 420163388868960)), (nat_lit 6765, Int.ofNat (nat_lit 497013244017840)), (nat_lit 6766, Int.ofNat (nat_lit 511430690355264)), (nat_lit 6767, Int.ofNat (nat_lit 735850357288200)), (nat_lit 6786, Int.ofNat (nat_lit 144526252156704)), (nat_lit 6787, Int.ofNat (nat_lit 324397015566624)), (nat_lit 6788, Int.ofNat (nat_lit 581962621382208)), (nat_lit 6789, Int.ofNat (nat_lit 633493976528160)), (nat_lit 6790, Int.ofNat (nat_lit 521271618266880)), (nat_lit 6791, Int.ofNat (nat_lit 777605283823104)), (nat_lit 6811, Int.ofNat (nat_lit 122940715654944)), (nat_lit 6812, Int.ofNat (nat_lit 496098769380192)), (nat_lit 6813, Int.ofNat (nat_lit 569514416012784)), (nat_lit 6814, Int.ofNat (nat_lit 438392507673408)), (nat_lit 6815, Int.ofNat (nat_lit 574036927094664)), (nat_lit 6836, Int.ofNat (nat_lit 375690508310304)), (nat_lit 6837, Int.ofNat (nat_lit 665149508233056)), (nat_lit 6838, Int.ofNat (nat_lit 474164878364160)), (nat_lit 6839, Int.ofNat (nat_lit 486459607582080)), (nat_lit 6861, Int.ofNat (nat_lit 229503465479376)), (nat_lit 6862, Int.ofNat (nat_lit 284380297379136)), (nat_lit 6863, Int.ofNat (nat_lit 305111741840136)), (nat_lit 6887, Int.ofNat (nat_lit 31657349589696)), (nat_lit 7212, Int.ofNat (nat_lit 3937964184000)), (nat_lit 7218, Int.ofNat (nat_lit 40371722785152)), (nat_lit 7220, Int.ofNat (nat_lit 44798908302720)), (nat_lit 7237, Int.ofNat (nat_lit 4621903070400)), (nat_lit 7240, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7241, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7242, Int.ofNat (nat_lit 71194290659712)), (nat_lit 7244, Int.ofNat (nat_lit 125183510939520)), (nat_lit 7245, Int.ofNat (nat_lit 48552573484800))]
theorem block030_data_flat159_step : block030_data_flat159 = (CoefficientMerge.trim block030_data_flat158) := by decide +kernel
theorem block030_data_flat159_original : block030_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded))))))))) := by
  rw [block030_data_flat159_step, block030_data_flat158_original]
theorem block030_data : block030 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5906946276000 : Int) atom2209Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6166081152000 : Int) atom2211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48198762938304 : Int) atom2212Coded) (CoefficientMerge.scale (55394670767040 : Int) atom2213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2214Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144759386217600 : Int) atom2216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13611889922400 : Int) atom2217Coded) (CoefficientMerge.scale (16959380961600 : Int) atom2218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15938788219200 : Int) atom2219Coded) (CoefficientMerge.scale (21084276628800 : Int) atom2220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26229765038400 : Int) atom2221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46202260100832 : Int) atom2222Coded) (CoefficientMerge.scale (81012310204320 : Int) atom2223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81642768253200 : Int) atom2224Coded) (CoefficientMerge.scale (163234772648640 : Int) atom2225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259266104559000 : Int) atom2226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22866327237600 : Int) atom2227Coded) (CoefficientMerge.scale (40619059588800 : Int) atom2228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46806403089600 : Int) atom2229Coded) (CoefficientMerge.scale (52993746590400 : Int) atom2230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61134145671456 : Int) atom2231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35750728427040 : Int) atom2232Coded) (CoefficientMerge.scale (134843930321760 : Int) atom2233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152999071608240 : Int) atom2234Coded) (CoefficientMerge.scale (238441743058464 : Int) atom2235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (351617123226600 : Int) atom2236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40354609125600 : Int) atom2237Coded) (CoefficientMerge.scale (73565069054400 : Int) atom2238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79773674904000 : Int) atom2239Coded) (CoefficientMerge.scale (108303700013856 : Int) atom2240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (93975053091840 : Int) atom2241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242404998392160 : Int) atom2242Coded) (CoefficientMerge.scale (281781574565040 : Int) atom2243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (317642421824064 : Int) atom2244Coded) (CoefficientMerge.scale (434543545384200 : Int) atom2245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58895377279200 : Int) atom2246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119916989438400 : Int) atom2247Coded) (CoefficientMerge.scale (139281009274656 : Int) atom2248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (147695343805440 : Int) atom2249Coded) (CoefficientMerge.scale (318868270558560 : Int) atom2250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375739893912240 : Int) atom2251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371302791372864 : Int) atom2252Coded) (CoefficientMerge.scale (579609785953800 : Int) atom2253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81915413580000 : Int) atom2254Coded) (CoefficientMerge.scale (185157426221856 : Int) atom2255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (221281111434240 : Int) atom2256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420163388868960 : Int) atom2257Coded) (CoefficientMerge.scale (497013244017840 : Int) atom2258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511430690355264 : Int) atom2259Coded) (CoefficientMerge.scale (735850357288200 : Int) atom2260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (144526252156704 : Int) atom2261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324397015566624 : Int) atom2262Coded) (CoefficientMerge.scale (581962621382208 : Int) atom2263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (633493976528160 : Int) atom2264Coded) (CoefficientMerge.scale (521271618266880 : Int) atom2265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777605283823104 : Int) atom2266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122940715654944 : Int) atom2267Coded) (CoefficientMerge.scale (496098769380192 : Int) atom2268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (569514416012784 : Int) atom2269Coded) (CoefficientMerge.scale (438392507673408 : Int) atom2270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (574036927094664 : Int) atom2271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375690508310304 : Int) atom2272Coded) (CoefficientMerge.scale (665149508233056 : Int) atom2273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (474164878364160 : Int) atom2274Coded) (CoefficientMerge.scale (486459607582080 : Int) atom2275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229503465479376 : Int) atom2276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284380297379136 : Int) atom2277Coded) (CoefficientMerge.scale (305111741840136 : Int) atom2278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31657349589696 : Int) atom2279Coded) (CoefficientMerge.scale (3937964184000 : Int) atom2280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40371722785152 : Int) atom2281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44798908302720 : Int) atom2282Coded) (CoefficientMerge.scale (4621903070400 : Int) atom2283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2284Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71194290659712 : Int) atom2286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125183510939520 : Int) atom2287Coded) (CoefficientMerge.scale (48552573484800 : Int) atom2288Coded)))))))) := by
  have h : block030 = block030_data_flat159 := by decide +kernel
  exact h.trans block030_data_flat159_original
theorem block030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block030 := by
  rw [block030_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2209Coded_nonneg g hg hA hB) (atom2210Coded_nonneg g hg hA hB)) (add_nonneg (atom2211Coded_nonneg g hg hA hB) (add_nonneg (atom2212Coded_nonneg g hg hA hB) (atom2213Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2214Coded_nonneg g hg hA hB) (atom2215Coded_nonneg g hg hA hB)) (add_nonneg (atom2216Coded_nonneg g hg hA hB) (add_nonneg (atom2217Coded_nonneg g hg hA hB) (atom2218Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2219Coded_nonneg g hg hA hB) (atom2220Coded_nonneg g hg hA hB)) (add_nonneg (atom2221Coded_nonneg g hg hA hB) (add_nonneg (atom2222Coded_nonneg g hg hA hB) (atom2223Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2224Coded_nonneg g hg hA hB) (atom2225Coded_nonneg g hg hA hB)) (add_nonneg (atom2226Coded_nonneg g hg hA hB) (add_nonneg (atom2227Coded_nonneg g hg hA hB) (atom2228Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2229Coded_nonneg g hg hA hB) (atom2230Coded_nonneg g hg hA hB)) (add_nonneg (atom2231Coded_nonneg g hg hA hB) (add_nonneg (atom2232Coded_nonneg g hg hA hB) (atom2233Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2234Coded_nonneg g hg hA hB) (atom2235Coded_nonneg g hg hA hB)) (add_nonneg (atom2236Coded_nonneg g hg hA hB) (add_nonneg (atom2237Coded_nonneg g hg hA hB) (atom2238Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2239Coded_nonneg g hg hA hB) (atom2240Coded_nonneg g hg hA hB)) (add_nonneg (atom2241Coded_nonneg g hg hA hB) (add_nonneg (atom2242Coded_nonneg g hg hA hB) (atom2243Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2244Coded_nonneg g hg hA hB) (atom2245Coded_nonneg g hg hA hB)) (add_nonneg (atom2246Coded_nonneg g hg hA hB) (add_nonneg (atom2247Coded_nonneg g hg hA hB) (atom2248Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2249Coded_nonneg g hg hA hB) (atom2250Coded_nonneg g hg hA hB)) (add_nonneg (atom2251Coded_nonneg g hg hA hB) (add_nonneg (atom2252Coded_nonneg g hg hA hB) (atom2253Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2254Coded_nonneg g hg hA hB) (atom2255Coded_nonneg g hg hA hB)) (add_nonneg (atom2256Coded_nonneg g hg hA hB) (add_nonneg (atom2257Coded_nonneg g hg hA hB) (atom2258Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2259Coded_nonneg g hg hA hB) (atom2260Coded_nonneg g hg hA hB)) (add_nonneg (atom2261Coded_nonneg g hg hA hB) (add_nonneg (atom2262Coded_nonneg g hg hA hB) (atom2263Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2264Coded_nonneg g hg hA hB) (atom2265Coded_nonneg g hg hA hB)) (add_nonneg (atom2266Coded_nonneg g hg hA hB) (add_nonneg (atom2267Coded_nonneg g hg hA hB) (atom2268Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2269Coded_nonneg g hg hA hB) (atom2270Coded_nonneg g hg hA hB)) (add_nonneg (atom2271Coded_nonneg g hg hA hB) (add_nonneg (atom2272Coded_nonneg g hg hA hB) (atom2273Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2274Coded_nonneg g hg hA hB) (atom2275Coded_nonneg g hg hA hB)) (add_nonneg (atom2276Coded_nonneg g hg hA hB) (add_nonneg (atom2277Coded_nonneg g hg hA hB) (atom2278Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2279Coded_nonneg g hg hA hB) (atom2280Coded_nonneg g hg hA hB)) (add_nonneg (atom2281Coded_nonneg g hg hA hB) (add_nonneg (atom2282Coded_nonneg g hg hA hB) (atom2283Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2284Coded_nonneg g hg hA hB) (atom2285Coded_nonneg g hg hA hB)) (add_nonneg (atom2286Coded_nonneg g hg hA hB) (add_nonneg (atom2287Coded_nonneg g hg hA hB) (atom2288Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
