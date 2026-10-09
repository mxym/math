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
def atom2204 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom2204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2204 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom2204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10703377792800 : Int) atom2204) := by
  rw [SparsePolynomial.eval_scale, eval_atom2204]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
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
def block029 : SparsePolynomial.Poly := [([10,11,23], 144759386217600), ([10,12,12], 11171370949200), ([10,12,13], 15674337756000), ([10,12,14], 20819826165600), ([10,12,15], 25965314575200), ([10,12,16], 31110802984800), ([10,12,17], 36256291394400), ([10,12,18], 45334222105392), ([10,12,20], 62475180994512), ([10,12,21], 74122873486200), ([10,12,22], 153208246292640), ([10,12,23], 247986262408500), ([10,13,13], 27104843581200), ([10,13,14], 48070183946400), ([10,13,15], 51174486871200), ([10,13,16], 57361830372000), ([10,13,17], 63549173872800), ([10,13,18], 73075050903888), ([10,13,19], 42531469390080), ([10,13,20], 123990436996272), ([10,13,21], 139283462035080), ([10,13,22], 231954760353888), ([10,13,23], 339742267533900), ([10,14,14], 43567217139600), ([10,14,15], 85125142317600), ([10,14,16], 91333748167200), ([10,14,17], 97542354016800), ([10,14,18], 98659441119888), ([10,14,19], 89005622222880), ([10,14,20], 181911628693872), ([10,14,21], 210902114186280), ([10,14,22], 296892084189888), ([10,14,23], 409342572985500), ([10,15,15], 67242842528400), ([10,15,16], 126342205466400), ([10,15,17], 131551480922400), ([10,15,18], 146424341228688), ([10,15,19], 141191439828480), ([10,15,20], 276800336879472), ([10,15,21], 323185034474280), ([10,15,22], 355765957502688), ([10,15,23], 469518281927100), ([10,16,16], 87867320864400), ([10,16,17], 175840953472800), ([10,16,18], 176455475967888), ([10,16,19], 188873223482880), ([10,16,20], 342132769449072), ([10,16,21], 402956051584680), ([10,16,22], 392182562174688), ([10,16,23], 595302229928700), ([10,17,17], 111950474605200), ([10,17,18], 221385718393488), ([10,17,19], 256420484052480), ([10,17,20], 432297048162672), ([10,17,21], 510042099453480), ([10,17,22], 515066696280288), ([10,17,23], 732260508695100), ([10,18,18], 155797451099136), ([10,18,19], 337443300433008), ([10,18,20], 574554396344544), ([10,18,21], 618751227702168), ([10,18,22], 510055392621024), ([10,18,23], 755578774750140), ([10,19,19], 118417314212208), ([10,19,20], 457772204848464), ([10,19,21], 509935380181128), ([10,19,22], 417231228435936), ([10,19,23], 516076854392700), ([10,20,20], 346547254740192), ([10,20,21], 577171780724088), ([10,20,22], 437315251001568), ([10,20,23], 473142522455676), ([10,21,21], 169648736717592), ([10,21,22], 230976346924512), ([10,21,23], 260856825525180), ([11,11,11], 10703377792800), ([11,11,12], 9249121728000), ([11,11,13], 6166081152000), ([11,11,14], 3083040576000), ([11,11,18], 11628748118592)]
theorem block029_data : block029 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (144759386217600 : Int) atom2129) (SparsePolynomial.scale (11171370949200 : Int) atom2130)) (SparsePolynomial.merge (SparsePolynomial.scale (15674337756000 : Int) atom2131) (SparsePolynomial.merge (SparsePolynomial.scale (20819826165600 : Int) atom2132) (SparsePolynomial.scale (25965314575200 : Int) atom2133)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31110802984800 : Int) atom2134) (SparsePolynomial.scale (36256291394400 : Int) atom2135)) (SparsePolynomial.merge (SparsePolynomial.scale (45334222105392 : Int) atom2136) (SparsePolynomial.merge (SparsePolynomial.scale (62475180994512 : Int) atom2137) (SparsePolynomial.scale (74122873486200 : Int) atom2138))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (153208246292640 : Int) atom2139) (SparsePolynomial.scale (247986262408500 : Int) atom2140)) (SparsePolynomial.merge (SparsePolynomial.scale (27104843581200 : Int) atom2141) (SparsePolynomial.merge (SparsePolynomial.scale (48070183946400 : Int) atom2142) (SparsePolynomial.scale (51174486871200 : Int) atom2143)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (57361830372000 : Int) atom2144) (SparsePolynomial.scale (63549173872800 : Int) atom2145)) (SparsePolynomial.merge (SparsePolynomial.scale (73075050903888 : Int) atom2146) (SparsePolynomial.merge (SparsePolynomial.scale (42531469390080 : Int) atom2147) (SparsePolynomial.scale (123990436996272 : Int) atom2148)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (139283462035080 : Int) atom2149) (SparsePolynomial.scale (231954760353888 : Int) atom2150)) (SparsePolynomial.merge (SparsePolynomial.scale (339742267533900 : Int) atom2151) (SparsePolynomial.merge (SparsePolynomial.scale (43567217139600 : Int) atom2152) (SparsePolynomial.scale (85125142317600 : Int) atom2153)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (91333748167200 : Int) atom2154) (SparsePolynomial.scale (97542354016800 : Int) atom2155)) (SparsePolynomial.merge (SparsePolynomial.scale (98659441119888 : Int) atom2156) (SparsePolynomial.merge (SparsePolynomial.scale (89005622222880 : Int) atom2157) (SparsePolynomial.scale (181911628693872 : Int) atom2158))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (210902114186280 : Int) atom2159) (SparsePolynomial.scale (296892084189888 : Int) atom2160)) (SparsePolynomial.merge (SparsePolynomial.scale (409342572985500 : Int) atom2161) (SparsePolynomial.merge (SparsePolynomial.scale (67242842528400 : Int) atom2162) (SparsePolynomial.scale (126342205466400 : Int) atom2163)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (131551480922400 : Int) atom2164) (SparsePolynomial.scale (146424341228688 : Int) atom2165)) (SparsePolynomial.merge (SparsePolynomial.scale (141191439828480 : Int) atom2166) (SparsePolynomial.merge (SparsePolynomial.scale (276800336879472 : Int) atom2167) (SparsePolynomial.scale (323185034474280 : Int) atom2168))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (355765957502688 : Int) atom2169) (SparsePolynomial.scale (469518281927100 : Int) atom2170)) (SparsePolynomial.merge (SparsePolynomial.scale (87867320864400 : Int) atom2171) (SparsePolynomial.merge (SparsePolynomial.scale (175840953472800 : Int) atom2172) (SparsePolynomial.scale (176455475967888 : Int) atom2173)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (188873223482880 : Int) atom2174) (SparsePolynomial.scale (342132769449072 : Int) atom2175)) (SparsePolynomial.merge (SparsePolynomial.scale (402956051584680 : Int) atom2176) (SparsePolynomial.merge (SparsePolynomial.scale (392182562174688 : Int) atom2177) (SparsePolynomial.scale (595302229928700 : Int) atom2178))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (111950474605200 : Int) atom2179) (SparsePolynomial.scale (221385718393488 : Int) atom2180)) (SparsePolynomial.merge (SparsePolynomial.scale (256420484052480 : Int) atom2181) (SparsePolynomial.merge (SparsePolynomial.scale (432297048162672 : Int) atom2182) (SparsePolynomial.scale (510042099453480 : Int) atom2183)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (515066696280288 : Int) atom2184) (SparsePolynomial.scale (732260508695100 : Int) atom2185)) (SparsePolynomial.merge (SparsePolynomial.scale (155797451099136 : Int) atom2186) (SparsePolynomial.merge (SparsePolynomial.scale (337443300433008 : Int) atom2187) (SparsePolynomial.scale (574554396344544 : Int) atom2188)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (618751227702168 : Int) atom2189) (SparsePolynomial.scale (510055392621024 : Int) atom2190)) (SparsePolynomial.merge (SparsePolynomial.scale (755578774750140 : Int) atom2191) (SparsePolynomial.merge (SparsePolynomial.scale (118417314212208 : Int) atom2192) (SparsePolynomial.scale (457772204848464 : Int) atom2193)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (509935380181128 : Int) atom2194) (SparsePolynomial.scale (417231228435936 : Int) atom2195)) (SparsePolynomial.merge (SparsePolynomial.scale (516076854392700 : Int) atom2196) (SparsePolynomial.merge (SparsePolynomial.scale (346547254740192 : Int) atom2197) (SparsePolynomial.scale (577171780724088 : Int) atom2198))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (437315251001568 : Int) atom2199) (SparsePolynomial.scale (473142522455676 : Int) atom2200)) (SparsePolynomial.merge (SparsePolynomial.scale (169648736717592 : Int) atom2201) (SparsePolynomial.merge (SparsePolynomial.scale (230976346924512 : Int) atom2202) (SparsePolynomial.scale (260856825525180 : Int) atom2203)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10703377792800 : Int) atom2204) (SparsePolynomial.scale (9249121728000 : Int) atom2205)) (SparsePolynomial.merge (SparsePolynomial.scale (6166081152000 : Int) atom2206) (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2207) (SparsePolynomial.scale (11628748118592 : Int) atom2208)))))))) := by decide +kernel
theorem block029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block029 := by
  rw [block029_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2129_nonneg g hg hA hB) (atom2130_nonneg g hg hA hB)) (add_nonneg (atom2131_nonneg g hg hA hB) (add_nonneg (atom2132_nonneg g hg hA hB) (atom2133_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2134_nonneg g hg hA hB) (atom2135_nonneg g hg hA hB)) (add_nonneg (atom2136_nonneg g hg hA hB) (add_nonneg (atom2137_nonneg g hg hA hB) (atom2138_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2139_nonneg g hg hA hB) (atom2140_nonneg g hg hA hB)) (add_nonneg (atom2141_nonneg g hg hA hB) (add_nonneg (atom2142_nonneg g hg hA hB) (atom2143_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2144_nonneg g hg hA hB) (atom2145_nonneg g hg hA hB)) (add_nonneg (atom2146_nonneg g hg hA hB) (add_nonneg (atom2147_nonneg g hg hA hB) (atom2148_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2149_nonneg g hg hA hB) (atom2150_nonneg g hg hA hB)) (add_nonneg (atom2151_nonneg g hg hA hB) (add_nonneg (atom2152_nonneg g hg hA hB) (atom2153_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2154_nonneg g hg hA hB) (atom2155_nonneg g hg hA hB)) (add_nonneg (atom2156_nonneg g hg hA hB) (add_nonneg (atom2157_nonneg g hg hA hB) (atom2158_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2159_nonneg g hg hA hB) (atom2160_nonneg g hg hA hB)) (add_nonneg (atom2161_nonneg g hg hA hB) (add_nonneg (atom2162_nonneg g hg hA hB) (atom2163_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2164_nonneg g hg hA hB) (atom2165_nonneg g hg hA hB)) (add_nonneg (atom2166_nonneg g hg hA hB) (add_nonneg (atom2167_nonneg g hg hA hB) (atom2168_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2169_nonneg g hg hA hB) (atom2170_nonneg g hg hA hB)) (add_nonneg (atom2171_nonneg g hg hA hB) (add_nonneg (atom2172_nonneg g hg hA hB) (atom2173_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2174_nonneg g hg hA hB) (atom2175_nonneg g hg hA hB)) (add_nonneg (atom2176_nonneg g hg hA hB) (add_nonneg (atom2177_nonneg g hg hA hB) (atom2178_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2179_nonneg g hg hA hB) (atom2180_nonneg g hg hA hB)) (add_nonneg (atom2181_nonneg g hg hA hB) (add_nonneg (atom2182_nonneg g hg hA hB) (atom2183_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2184_nonneg g hg hA hB) (atom2185_nonneg g hg hA hB)) (add_nonneg (atom2186_nonneg g hg hA hB) (add_nonneg (atom2187_nonneg g hg hA hB) (atom2188_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2189_nonneg g hg hA hB) (atom2190_nonneg g hg hA hB)) (add_nonneg (atom2191_nonneg g hg hA hB) (add_nonneg (atom2192_nonneg g hg hA hB) (atom2193_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2194_nonneg g hg hA hB) (atom2195_nonneg g hg hA hB)) (add_nonneg (atom2196_nonneg g hg hA hB) (add_nonneg (atom2197_nonneg g hg hA hB) (atom2198_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2199_nonneg g hg hA hB) (atom2200_nonneg g hg hA hB)) (add_nonneg (atom2201_nonneg g hg hA hB) (add_nonneg (atom2202_nonneg g hg hA hB) (atom2203_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2204_nonneg g hg hA hB) (atom2205_nonneg g hg hA hB)) (add_nonneg (atom2206_nonneg g hg hA hB) (add_nonneg (atom2207_nonneg g hg hA hB) (atom2208_nonneg g hg hA hB))))))))

end APPT.Finite24
