import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2209 : SparsePolynomial.Poly := [([11,12,12], 1)]
theorem eval_atom2209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2209 = ((g 11) * (g 12) * (g 12)) := by
  norm_num [atom2209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5906946276000 : Int) atom2209) := by
  rw [SparsePolynomial.eval_scale, eval_atom2209]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2210 : SparsePolynomial.Poly := [([11,12,16], 1)]
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
def atom2211 : SparsePolynomial.Poly := [([11,12,17], 1)]
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
def atom2212 : SparsePolynomial.Poly := [([11,12,18], 1)]
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
def atom2213 : SparsePolynomial.Poly := [([11,12,20], 1)]
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
def atom2214 : SparsePolynomial.Poly := [([11,12,21], 1)]
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
def atom2215 : SparsePolynomial.Poly := [([11,12,22], 1)]
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
def atom2216 : SparsePolynomial.Poly := [([11,12,23], 1)]
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
def atom2217 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom2217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2217 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom2217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13611889922400 : Int) atom2217) := by
  rw [SparsePolynomial.eval_scale, eval_atom2217]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2218 : SparsePolynomial.Poly := [([11,13,14], 1)]
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
def atom2219 : SparsePolynomial.Poly := [([11,13,15], 1)]
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
def atom2220 : SparsePolynomial.Poly := [([11,13,16], 1)]
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
def atom2221 : SparsePolynomial.Poly := [([11,13,17], 1)]
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
def atom2222 : SparsePolynomial.Poly := [([11,13,18], 1)]
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
def atom2223 : SparsePolynomial.Poly := [([11,13,20], 1)]
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
def atom2224 : SparsePolynomial.Poly := [([11,13,21], 1)]
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
def atom2225 : SparsePolynomial.Poly := [([11,13,22], 1)]
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
def atom2226 : SparsePolynomial.Poly := [([11,13,23], 1)]
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
def atom2227 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom2227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2227 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom2227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22866327237600 : Int) atom2227) := by
  rw [SparsePolynomial.eval_scale, eval_atom2227]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2228 : SparsePolynomial.Poly := [([11,14,15], 1)]
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
def atom2229 : SparsePolynomial.Poly := [([11,14,16], 1)]
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
def atom2230 : SparsePolynomial.Poly := [([11,14,17], 1)]
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
def atom2231 : SparsePolynomial.Poly := [([11,14,18], 1)]
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
def atom2232 : SparsePolynomial.Poly := [([11,14,19], 1)]
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
def atom2233 : SparsePolynomial.Poly := [([11,14,20], 1)]
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
def atom2234 : SparsePolynomial.Poly := [([11,14,21], 1)]
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
def atom2235 : SparsePolynomial.Poly := [([11,14,22], 1)]
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
def atom2236 : SparsePolynomial.Poly := [([11,14,23], 1)]
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
def atom2237 : SparsePolynomial.Poly := [([11,15,15], 1)]
theorem eval_atom2237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2237 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom2237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40354609125600 : Int) atom2237) := by
  rw [SparsePolynomial.eval_scale, eval_atom2237]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2238 : SparsePolynomial.Poly := [([11,15,16], 1)]
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
def atom2239 : SparsePolynomial.Poly := [([11,15,17], 1)]
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
def atom2240 : SparsePolynomial.Poly := [([11,15,18], 1)]
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
def atom2241 : SparsePolynomial.Poly := [([11,15,19], 1)]
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
def atom2242 : SparsePolynomial.Poly := [([11,15,20], 1)]
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
def atom2243 : SparsePolynomial.Poly := [([11,15,21], 1)]
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
def atom2244 : SparsePolynomial.Poly := [([11,15,22], 1)]
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
def atom2245 : SparsePolynomial.Poly := [([11,15,23], 1)]
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
def atom2246 : SparsePolynomial.Poly := [([11,16,16], 1)]
theorem eval_atom2246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2246 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom2246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58895377279200 : Int) atom2246) := by
  rw [SparsePolynomial.eval_scale, eval_atom2246]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2247 : SparsePolynomial.Poly := [([11,16,17], 1)]
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
def atom2248 : SparsePolynomial.Poly := [([11,16,18], 1)]
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
def atom2249 : SparsePolynomial.Poly := [([11,16,19], 1)]
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
def atom2250 : SparsePolynomial.Poly := [([11,16,20], 1)]
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
def atom2251 : SparsePolynomial.Poly := [([11,16,21], 1)]
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
def atom2252 : SparsePolynomial.Poly := [([11,16,22], 1)]
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
def atom2253 : SparsePolynomial.Poly := [([11,16,23], 1)]
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
def atom2254 : SparsePolynomial.Poly := [([11,17,17], 1)]
theorem eval_atom2254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2254 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom2254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81915413580000 : Int) atom2254) := by
  rw [SparsePolynomial.eval_scale, eval_atom2254]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2255 : SparsePolynomial.Poly := [([11,17,18], 1)]
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
def atom2256 : SparsePolynomial.Poly := [([11,17,19], 1)]
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
def atom2257 : SparsePolynomial.Poly := [([11,17,20], 1)]
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
def atom2258 : SparsePolynomial.Poly := [([11,17,21], 1)]
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
def atom2259 : SparsePolynomial.Poly := [([11,17,22], 1)]
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
def atom2260 : SparsePolynomial.Poly := [([11,17,23], 1)]
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
def atom2261 : SparsePolynomial.Poly := [([11,18,18], 1)]
theorem eval_atom2261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2261 = ((g 11) * (g 18) * (g 18)) := by
  norm_num [atom2261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144526252156704 : Int) atom2261) := by
  rw [SparsePolynomial.eval_scale, eval_atom2261]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 11) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2262 : SparsePolynomial.Poly := [([11,18,19], 1)]
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
def atom2263 : SparsePolynomial.Poly := [([11,18,20], 1)]
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
def atom2264 : SparsePolynomial.Poly := [([11,18,21], 1)]
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
def atom2265 : SparsePolynomial.Poly := [([11,18,22], 1)]
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
def atom2266 : SparsePolynomial.Poly := [([11,18,23], 1)]
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
def atom2267 : SparsePolynomial.Poly := [([11,19,19], 1)]
theorem eval_atom2267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2267 = ((g 11) * (g 19) * (g 19)) := by
  norm_num [atom2267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122940715654944 : Int) atom2267) := by
  rw [SparsePolynomial.eval_scale, eval_atom2267]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2268 : SparsePolynomial.Poly := [([11,19,20], 1)]
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
def atom2269 : SparsePolynomial.Poly := [([11,19,21], 1)]
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
def atom2270 : SparsePolynomial.Poly := [([11,19,22], 1)]
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
def atom2271 : SparsePolynomial.Poly := [([11,19,23], 1)]
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
def atom2272 : SparsePolynomial.Poly := [([11,20,20], 1)]
theorem eval_atom2272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2272 = ((g 11) * (g 20) * (g 20)) := by
  norm_num [atom2272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375690508310304 : Int) atom2272) := by
  rw [SparsePolynomial.eval_scale, eval_atom2272]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2273 : SparsePolynomial.Poly := [([11,20,21], 1)]
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
def atom2274 : SparsePolynomial.Poly := [([11,20,22], 1)]
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
def atom2275 : SparsePolynomial.Poly := [([11,20,23], 1)]
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
def atom2276 : SparsePolynomial.Poly := [([11,21,21], 1)]
theorem eval_atom2276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2276 = ((g 11) * (g 21) * (g 21)) := by
  norm_num [atom2276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229503465479376 : Int) atom2276) := by
  rw [SparsePolynomial.eval_scale, eval_atom2276]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 11) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2277 : SparsePolynomial.Poly := [([11,21,22], 1)]
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
def atom2278 : SparsePolynomial.Poly := [([11,21,23], 1)]
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
def atom2279 : SparsePolynomial.Poly := [([11,22,23], 1)]
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
def atom2280 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom2280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2280 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom2280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3937964184000 : Int) atom2280) := by
  rw [SparsePolynomial.eval_scale, eval_atom2280]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2281 : SparsePolynomial.Poly := [([12,12,18], 1)]
theorem eval_atom2281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2281 = ((g 12) * (g 12) * (g 18)) := by
  norm_num [atom2281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40371722785152 : Int) atom2281) := by
  rw [SparsePolynomial.eval_scale, eval_atom2281]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2282 : SparsePolynomial.Poly := [([12,12,20], 1)]
theorem eval_atom2282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2282 = ((g 12) * (g 12) * (g 20)) := by
  norm_num [atom2282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44798908302720 : Int) atom2282) := by
  rw [SparsePolynomial.eval_scale, eval_atom2282]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2283 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom2283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2283 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom2283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4621903070400 : Int) atom2283) := by
  rw [SparsePolynomial.eval_scale, eval_atom2283]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2284 : SparsePolynomial.Poly := [([12,13,16], 1)]
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
def atom2285 : SparsePolynomial.Poly := [([12,13,17], 1)]
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
def atom2286 : SparsePolynomial.Poly := [([12,13,18], 1)]
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
def atom2287 : SparsePolynomial.Poly := [([12,13,20], 1)]
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
def atom2288 : SparsePolynomial.Poly := [([12,13,21], 1)]
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
def block030 : SparsePolynomial.Poly := [([11,12,12], 5906946276000), ([11,12,16], 3083040576000), ([11,12,17], 6166081152000), ([11,12,18], 48198762938304), ([11,12,20], 55394670767040), ([11,12,21], 48552573484800), ([11,12,22], 93303439004160), ([11,12,23], 144759386217600), ([11,13,13], 13611889922400), ([11,13,14], 16959380961600), ([11,13,15], 15938788219200), ([11,13,16], 21084276628800), ([11,13,17], 26229765038400), ([11,13,18], 46202260100832), ([11,13,20], 81012310204320), ([11,13,21], 81642768253200), ([11,13,22], 163234772648640), ([11,13,23], 259266104559000), ([11,14,14], 22866327237600), ([11,14,15], 40619059588800), ([11,14,16], 46806403089600), ([11,14,17], 52993746590400), ([11,14,18], 61134145671456), ([11,14,19], 35750728427040), ([11,14,20], 134843930321760), ([11,14,21], 152999071608240), ([11,14,22], 238441743058464), ([11,14,23], 351617123226600), ([11,15,15], 40354609125600), ([11,15,16], 73565069054400), ([11,15,17], 79773674904000), ([11,15,18], 108303700013856), ([11,15,19], 93975053091840), ([11,15,20], 242404998392160), ([11,15,21], 281781574565040), ([11,15,22], 317642421824064), ([11,15,23], 434543545384200), ([11,16,16], 58895377279200), ([11,16,17], 119916989438400), ([11,16,18], 139281009274656), ([11,16,19], 147695343805440), ([11,16,20], 318868270558560), ([11,16,21], 375739893912240), ([11,16,22], 371302791372864), ([11,16,23], 579609785953800), ([11,17,17], 81915413580000), ([11,17,18], 185157426221856), ([11,17,19], 221281111434240), ([11,17,20], 420163388868960), ([11,17,21], 497013244017840), ([11,17,22], 511430690355264), ([11,17,23], 735850357288200), ([11,18,18], 144526252156704), ([11,18,19], 324397015566624), ([11,18,20], 581962621382208), ([11,18,21], 633493976528160), ([11,18,22], 521271618266880), ([11,18,23], 777605283823104), ([11,19,19], 122940715654944), ([11,19,20], 496098769380192), ([11,19,21], 569514416012784), ([11,19,22], 438392507673408), ([11,19,23], 574036927094664), ([11,20,20], 375690508310304), ([11,20,21], 665149508233056), ([11,20,22], 474164878364160), ([11,20,23], 486459607582080), ([11,21,21], 229503465479376), ([11,21,22], 284380297379136), ([11,21,23], 305111741840136), ([11,22,23], 31657349589696), ([12,12,12], 3937964184000), ([12,12,18], 40371722785152), ([12,12,20], 44798908302720), ([12,13,13], 4621903070400), ([12,13,16], 3083040576000), ([12,13,17], 6166081152000), ([12,13,18], 71194290659712), ([12,13,20], 125183510939520), ([12,13,21], 48552573484800)]
theorem block030_data : block030 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5906946276000 : Int) atom2209) (SparsePolynomial.scale (3083040576000 : Int) atom2210)) (SparsePolynomial.merge (SparsePolynomial.scale (6166081152000 : Int) atom2211) (SparsePolynomial.merge (SparsePolynomial.scale (48198762938304 : Int) atom2212) (SparsePolynomial.scale (55394670767040 : Int) atom2213)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48552573484800 : Int) atom2214) (SparsePolynomial.scale (93303439004160 : Int) atom2215)) (SparsePolynomial.merge (SparsePolynomial.scale (144759386217600 : Int) atom2216) (SparsePolynomial.merge (SparsePolynomial.scale (13611889922400 : Int) atom2217) (SparsePolynomial.scale (16959380961600 : Int) atom2218))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15938788219200 : Int) atom2219) (SparsePolynomial.scale (21084276628800 : Int) atom2220)) (SparsePolynomial.merge (SparsePolynomial.scale (26229765038400 : Int) atom2221) (SparsePolynomial.merge (SparsePolynomial.scale (46202260100832 : Int) atom2222) (SparsePolynomial.scale (81012310204320 : Int) atom2223)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (81642768253200 : Int) atom2224) (SparsePolynomial.scale (163234772648640 : Int) atom2225)) (SparsePolynomial.merge (SparsePolynomial.scale (259266104559000 : Int) atom2226) (SparsePolynomial.merge (SparsePolynomial.scale (22866327237600 : Int) atom2227) (SparsePolynomial.scale (40619059588800 : Int) atom2228)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (46806403089600 : Int) atom2229) (SparsePolynomial.scale (52993746590400 : Int) atom2230)) (SparsePolynomial.merge (SparsePolynomial.scale (61134145671456 : Int) atom2231) (SparsePolynomial.merge (SparsePolynomial.scale (35750728427040 : Int) atom2232) (SparsePolynomial.scale (134843930321760 : Int) atom2233)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (152999071608240 : Int) atom2234) (SparsePolynomial.scale (238441743058464 : Int) atom2235)) (SparsePolynomial.merge (SparsePolynomial.scale (351617123226600 : Int) atom2236) (SparsePolynomial.merge (SparsePolynomial.scale (40354609125600 : Int) atom2237) (SparsePolynomial.scale (73565069054400 : Int) atom2238))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (79773674904000 : Int) atom2239) (SparsePolynomial.scale (108303700013856 : Int) atom2240)) (SparsePolynomial.merge (SparsePolynomial.scale (93975053091840 : Int) atom2241) (SparsePolynomial.merge (SparsePolynomial.scale (242404998392160 : Int) atom2242) (SparsePolynomial.scale (281781574565040 : Int) atom2243)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (317642421824064 : Int) atom2244) (SparsePolynomial.scale (434543545384200 : Int) atom2245)) (SparsePolynomial.merge (SparsePolynomial.scale (58895377279200 : Int) atom2246) (SparsePolynomial.merge (SparsePolynomial.scale (119916989438400 : Int) atom2247) (SparsePolynomial.scale (139281009274656 : Int) atom2248))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (147695343805440 : Int) atom2249) (SparsePolynomial.scale (318868270558560 : Int) atom2250)) (SparsePolynomial.merge (SparsePolynomial.scale (375739893912240 : Int) atom2251) (SparsePolynomial.merge (SparsePolynomial.scale (371302791372864 : Int) atom2252) (SparsePolynomial.scale (579609785953800 : Int) atom2253)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (81915413580000 : Int) atom2254) (SparsePolynomial.scale (185157426221856 : Int) atom2255)) (SparsePolynomial.merge (SparsePolynomial.scale (221281111434240 : Int) atom2256) (SparsePolynomial.merge (SparsePolynomial.scale (420163388868960 : Int) atom2257) (SparsePolynomial.scale (497013244017840 : Int) atom2258))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (511430690355264 : Int) atom2259) (SparsePolynomial.scale (735850357288200 : Int) atom2260)) (SparsePolynomial.merge (SparsePolynomial.scale (144526252156704 : Int) atom2261) (SparsePolynomial.merge (SparsePolynomial.scale (324397015566624 : Int) atom2262) (SparsePolynomial.scale (581962621382208 : Int) atom2263)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (633493976528160 : Int) atom2264) (SparsePolynomial.scale (521271618266880 : Int) atom2265)) (SparsePolynomial.merge (SparsePolynomial.scale (777605283823104 : Int) atom2266) (SparsePolynomial.merge (SparsePolynomial.scale (122940715654944 : Int) atom2267) (SparsePolynomial.scale (496098769380192 : Int) atom2268)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (569514416012784 : Int) atom2269) (SparsePolynomial.scale (438392507673408 : Int) atom2270)) (SparsePolynomial.merge (SparsePolynomial.scale (574036927094664 : Int) atom2271) (SparsePolynomial.merge (SparsePolynomial.scale (375690508310304 : Int) atom2272) (SparsePolynomial.scale (665149508233056 : Int) atom2273)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (474164878364160 : Int) atom2274) (SparsePolynomial.scale (486459607582080 : Int) atom2275)) (SparsePolynomial.merge (SparsePolynomial.scale (229503465479376 : Int) atom2276) (SparsePolynomial.merge (SparsePolynomial.scale (284380297379136 : Int) atom2277) (SparsePolynomial.scale (305111741840136 : Int) atom2278))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31657349589696 : Int) atom2279) (SparsePolynomial.scale (3937964184000 : Int) atom2280)) (SparsePolynomial.merge (SparsePolynomial.scale (40371722785152 : Int) atom2281) (SparsePolynomial.merge (SparsePolynomial.scale (44798908302720 : Int) atom2282) (SparsePolynomial.scale (4621903070400 : Int) atom2283)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2284) (SparsePolynomial.scale (6166081152000 : Int) atom2285)) (SparsePolynomial.merge (SparsePolynomial.scale (71194290659712 : Int) atom2286) (SparsePolynomial.merge (SparsePolynomial.scale (125183510939520 : Int) atom2287) (SparsePolynomial.scale (48552573484800 : Int) atom2288)))))))) := by decide +kernel
theorem block030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block030 := by
  rw [block030_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2209_nonneg g hg hA hB) (atom2210_nonneg g hg hA hB)) (add_nonneg (atom2211_nonneg g hg hA hB) (add_nonneg (atom2212_nonneg g hg hA hB) (atom2213_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2214_nonneg g hg hA hB) (atom2215_nonneg g hg hA hB)) (add_nonneg (atom2216_nonneg g hg hA hB) (add_nonneg (atom2217_nonneg g hg hA hB) (atom2218_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2219_nonneg g hg hA hB) (atom2220_nonneg g hg hA hB)) (add_nonneg (atom2221_nonneg g hg hA hB) (add_nonneg (atom2222_nonneg g hg hA hB) (atom2223_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2224_nonneg g hg hA hB) (atom2225_nonneg g hg hA hB)) (add_nonneg (atom2226_nonneg g hg hA hB) (add_nonneg (atom2227_nonneg g hg hA hB) (atom2228_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2229_nonneg g hg hA hB) (atom2230_nonneg g hg hA hB)) (add_nonneg (atom2231_nonneg g hg hA hB) (add_nonneg (atom2232_nonneg g hg hA hB) (atom2233_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2234_nonneg g hg hA hB) (atom2235_nonneg g hg hA hB)) (add_nonneg (atom2236_nonneg g hg hA hB) (add_nonneg (atom2237_nonneg g hg hA hB) (atom2238_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2239_nonneg g hg hA hB) (atom2240_nonneg g hg hA hB)) (add_nonneg (atom2241_nonneg g hg hA hB) (add_nonneg (atom2242_nonneg g hg hA hB) (atom2243_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2244_nonneg g hg hA hB) (atom2245_nonneg g hg hA hB)) (add_nonneg (atom2246_nonneg g hg hA hB) (add_nonneg (atom2247_nonneg g hg hA hB) (atom2248_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2249_nonneg g hg hA hB) (atom2250_nonneg g hg hA hB)) (add_nonneg (atom2251_nonneg g hg hA hB) (add_nonneg (atom2252_nonneg g hg hA hB) (atom2253_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2254_nonneg g hg hA hB) (atom2255_nonneg g hg hA hB)) (add_nonneg (atom2256_nonneg g hg hA hB) (add_nonneg (atom2257_nonneg g hg hA hB) (atom2258_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2259_nonneg g hg hA hB) (atom2260_nonneg g hg hA hB)) (add_nonneg (atom2261_nonneg g hg hA hB) (add_nonneg (atom2262_nonneg g hg hA hB) (atom2263_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2264_nonneg g hg hA hB) (atom2265_nonneg g hg hA hB)) (add_nonneg (atom2266_nonneg g hg hA hB) (add_nonneg (atom2267_nonneg g hg hA hB) (atom2268_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2269_nonneg g hg hA hB) (atom2270_nonneg g hg hA hB)) (add_nonneg (atom2271_nonneg g hg hA hB) (add_nonneg (atom2272_nonneg g hg hA hB) (atom2273_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2274_nonneg g hg hA hB) (atom2275_nonneg g hg hA hB)) (add_nonneg (atom2276_nonneg g hg hA hB) (add_nonneg (atom2277_nonneg g hg hA hB) (atom2278_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2279_nonneg g hg hA hB) (atom2280_nonneg g hg hA hB)) (add_nonneg (atom2281_nonneg g hg hA hB) (add_nonneg (atom2282_nonneg g hg hA hB) (atom2283_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2284_nonneg g hg hA hB) (atom2285_nonneg g hg hA hB)) (add_nonneg (atom2286_nonneg g hg hA hB) (add_nonneg (atom2287_nonneg g hg hA hB) (atom2288_nonneg g hg hA hB))))))))

end APPT.Finite24
