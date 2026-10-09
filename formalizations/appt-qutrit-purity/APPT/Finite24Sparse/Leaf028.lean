import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2049 : SparsePolynomial.Poly := [([9,12,15], 1)]
theorem eval_atom2049 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2049 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom2049, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2049_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38340001576800 : Int) atom2049) := by
  rw [SparsePolynomial.eval_scale, eval_atom2049]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2050 : SparsePolynomial.Poly := [([9,12,16], 1)]
theorem eval_atom2050 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2050 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom2050, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2050_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44527345077600 : Int) atom2050) := by
  rw [SparsePolynomial.eval_scale, eval_atom2050]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2051 : SparsePolynomial.Poly := [([9,12,17], 1)]
theorem eval_atom2051 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2051 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom2051, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2051_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50714688578400 : Int) atom2051) := by
  rw [SparsePolynomial.eval_scale, eval_atom2051]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2052 : SparsePolynomial.Poly := [([9,12,18], 1)]
theorem eval_atom2052 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2052 = ((g 9) * (g 12) * (g 18)) := by
  norm_num [atom2052, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2052_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73791992737584 : Int) atom2052) := by
  rw [SparsePolynomial.eval_scale, eval_atom2052]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2053 : SparsePolynomial.Poly := [([9,12,19], 1)]
theorem eval_atom2053 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2053 = ((g 9) * (g 12) * (g 19)) := by
  norm_num [atom2053, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2053_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44842698616320 : Int) atom2053) := by
  rw [SparsePolynomial.eval_scale, eval_atom2053]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2054 : SparsePolynomial.Poly := [([9,12,20], 1)]
theorem eval_atom2054 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2054 = ((g 9) * (g 12) * (g 20)) := by
  norm_num [atom2054, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2054_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125939444689872 : Int) atom2054) := by
  rw [SparsePolynomial.eval_scale, eval_atom2054]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2055 : SparsePolynomial.Poly := [([9,12,21], 1)]
theorem eval_atom2055 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2055 = ((g 9) * (g 12) * (g 21)) := by
  norm_num [atom2055, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2055_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (151220555232120 : Int) atom2055) := by
  rw [SparsePolynomial.eval_scale, eval_atom2055]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2056 : SparsePolynomial.Poly := [([9,12,22], 1)]
theorem eval_atom2056 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2056 = ((g 9) * (g 12) * (g 22)) := by
  norm_num [atom2056, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2056_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (246175983184032 : Int) atom2056) := by
  rw [SparsePolynomial.eval_scale, eval_atom2056]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2057 : SparsePolynomial.Poly := [([9,12,23], 1)]
theorem eval_atom2057 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2057 = ((g 9) * (g 12) * (g 23)) := by
  norm_num [atom2057, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2057_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (354181063490100 : Int) atom2057) := by
  rw [SparsePolynomial.eval_scale, eval_atom2057]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2058 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom2058 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2058 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom2058, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2058_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34312779824400 : Int) atom2058) := by
  rw [SparsePolynomial.eval_scale, eval_atom2058]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2059 : SparsePolynomial.Poly := [([9,13,14], 1)]
theorem eval_atom2059 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2059 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom2059, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2059_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62507318781600 : Int) atom2059) := by
  rw [SparsePolynomial.eval_scale, eval_atom2059]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2060 : SparsePolynomial.Poly := [([9,13,15], 1)]
theorem eval_atom2060 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2060 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom2060, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2060_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65632884055200 : Int) atom2060) := by
  rw [SparsePolynomial.eval_scale, eval_atom2060]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2061 : SparsePolynomial.Poly := [([9,13,16], 1)]
theorem eval_atom2061 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2061 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom2061, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2061_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71841489904800 : Int) atom2061) := by
  rw [SparsePolynomial.eval_scale, eval_atom2061]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2062 : SparsePolynomial.Poly := [([9,13,17], 1)]
theorem eval_atom2062 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2062 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom2062, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2062_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78050095754400 : Int) atom2062) := by
  rw [SparsePolynomial.eval_scale, eval_atom2062]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2063 : SparsePolynomial.Poly := [([9,13,18], 1)]
theorem eval_atom2063 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2063 = ((g 9) * (g 13) * (g 18)) := by
  norm_num [atom2063, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2063_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101889785997648 : Int) atom2063) := by
  rw [SparsePolynomial.eval_scale, eval_atom2063]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2064 : SparsePolynomial.Poly := [([9,13,19], 1)]
theorem eval_atom2064 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2064 = ((g 9) * (g 13) * (g 19)) := by
  norm_num [atom2064, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2064_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86927253684480 : Int) atom2064) := by
  rw [SparsePolynomial.eval_scale, eval_atom2064]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2065 : SparsePolynomial.Poly := [([9,13,20], 1)]
theorem eval_atom2065 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2065 = ((g 9) * (g 13) * (g 20)) := by
  norm_num [atom2065, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2065_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (183967270491312 : Int) atom2065) := by
  rw [SparsePolynomial.eval_scale, eval_atom2065]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2066 : SparsePolynomial.Poly := [([9,13,21], 1)]
theorem eval_atom2066 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2066 = ((g 9) * (g 13) * (g 21)) := by
  norm_num [atom2066, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2066_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (210863159270280 : Int) atom2066) := by
  rw [SparsePolynomial.eval_scale, eval_atom2066]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2067 : SparsePolynomial.Poly := [([9,13,22], 1)]
theorem eval_atom2067 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2067 = ((g 9) * (g 13) * (g 22)) := by
  norm_num [atom2067, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2067_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (315137321329248 : Int) atom2067) := by
  rw [SparsePolynomial.eval_scale, eval_atom2067]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2068 : SparsePolynomial.Poly := [([9,13,23], 1)]
theorem eval_atom2068 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2068 = ((g 9) * (g 13) * (g 23)) := by
  norm_num [atom2068, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2068_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (431271363530700 : Int) atom2068) := by
  rw [SparsePolynomial.eval_scale, eval_atom2068]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2069 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom2069 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2069 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom2069, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2069_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53879456307600 : Int) atom2069) := by
  rw [SparsePolynomial.eval_scale, eval_atom2069]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2070 : SparsePolynomial.Poly := [([9,14,15], 1)]
theorem eval_atom2070 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2070 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom2070, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2070_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104750290260000 : Int) atom2070) := by
  rw [SparsePolynomial.eval_scale, eval_atom2070]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2071 : SparsePolynomial.Poly := [([9,14,16], 1)]
theorem eval_atom2071 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2071 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom2071, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2071_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109959565716000 : Int) atom2071) := by
  rw [SparsePolynomial.eval_scale, eval_atom2071]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2072 : SparsePolynomial.Poly := [([9,14,17], 1)]
theorem eval_atom2072 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2072 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom2072, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2072_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (115168841172000 : Int) atom2072) := by
  rw [SparsePolynomial.eval_scale, eval_atom2072]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2073 : SparsePolynomial.Poly := [([9,14,18], 1)]
theorem eval_atom2073 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2073 = ((g 9) * (g 14) * (g 18)) := by
  norm_num [atom2073, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2073_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126017705320848 : Int) atom2073) := by
  rw [SparsePolynomial.eval_scale, eval_atom2073]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2074 : SparsePolynomial.Poly := [([9,14,19], 1)]
theorem eval_atom2074 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2074 = ((g 9) * (g 14) * (g 19)) := by
  norm_num [atom2074, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2074_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (127362899458080 : Int) atom2074) := by
  rw [SparsePolynomial.eval_scale, eval_atom2074]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2075 : SparsePolynomial.Poly := [([9,14,20], 1)]
theorem eval_atom2075 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2075 = ((g 9) * (g 14) * (g 20)) := by
  norm_num [atom2075, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2075_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (231267918963312 : Int) atom2075) := by
  rw [SparsePolynomial.eval_scale, eval_atom2075]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2076 : SparsePolynomial.Poly := [([9,14,21], 1)]
theorem eval_atom2076 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2076 = ((g 9) * (g 14) * (g 21)) := by
  norm_num [atom2076, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2076_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269059953741480 : Int) atom2076) := by
  rw [SparsePolynomial.eval_scale, eval_atom2076]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2077 : SparsePolynomial.Poly := [([9,14,22], 1)]
theorem eval_atom2077 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2077 = ((g 9) * (g 14) * (g 22)) := by
  norm_num [atom2077, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2077_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (363851473030848 : Int) atom2077) := by
  rw [SparsePolynomial.eval_scale, eval_atom2077]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2078 : SparsePolynomial.Poly := [([9,14,23], 1)]
theorem eval_atom2078 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2078 = ((g 9) * (g 14) * (g 23)) := by
  norm_num [atom2078, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2078_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (482737543249500 : Int) atom2078) := by
  rw [SparsePolynomial.eval_scale, eval_atom2078]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2079 : SparsePolynomial.Poly := [([9,15,15], 1)]
theorem eval_atom2079 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2079 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom2079, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2079_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79638791878800 : Int) atom2079) := by
  rw [SparsePolynomial.eval_scale, eval_atom2079]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2080 : SparsePolynomial.Poly := [([9,15,16], 1)]
theorem eval_atom2080 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2080 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom2080, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2080_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149114181031200 : Int) atom2080) := by
  rw [SparsePolynomial.eval_scale, eval_atom2080]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2081 : SparsePolynomial.Poly := [([9,15,17], 1)]
theorem eval_atom2081 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2081 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom2081, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2081_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152303533351200 : Int) atom2081) := by
  rw [SparsePolynomial.eval_scale, eval_atom2081]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2082 : SparsePolynomial.Poly := [([9,15,18], 1)]
theorem eval_atom2082 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2082 = ((g 9) * (g 15) * (g 18)) := by
  norm_num [atom2082, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2082_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (172326134536848 : Int) atom2082) := by
  rw [SparsePolynomial.eval_scale, eval_atom2082]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2083 : SparsePolynomial.Poly := [([9,15,19], 1)]
theorem eval_atom2083 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2083 = ((g 9) * (g 15) * (g 19)) := by
  norm_num [atom2083, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2083_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (173510210004480 : Int) atom2083) := by
  rw [SparsePolynomial.eval_scale, eval_atom2083]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2084 : SparsePolynomial.Poly := [([9,15,20], 1)]
theorem eval_atom2084 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2084 = ((g 9) * (g 15) * (g 20)) := by
  norm_num [atom2084, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2084_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (315536083923312 : Int) atom2084) := by
  rw [SparsePolynomial.eval_scale, eval_atom2084]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2085 : SparsePolynomial.Poly := [([9,15,21], 1)]
theorem eval_atom2085 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2085 = ((g 9) * (g 15) * (g 21)) := by
  norm_num [atom2085, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2085_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (367921016349480 : Int) atom2085) := by
  rw [SparsePolynomial.eval_scale, eval_atom2085]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2086 : SparsePolynomial.Poly := [([9,15,22], 1)]
theorem eval_atom2086 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2086 = ((g 9) * (g 15) * (g 22)) := by
  norm_num [atom2086, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2086_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (406502174209248 : Int) atom2086) := by
  rw [SparsePolynomial.eval_scale, eval_atom2086]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2087 : SparsePolynomial.Poly := [([9,15,23], 1)]
theorem eval_atom2087 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2087 = ((g 9) * (g 15) * (g 23)) := by
  norm_num [atom2087, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2087_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (524779126458300 : Int) atom2087) := by
  rw [SparsePolynomial.eval_scale, eval_atom2087]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2088 : SparsePolynomial.Poly := [([9,16,16], 1)]
theorem eval_atom2088 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2088 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom2088, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2088_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101326387654800 : Int) atom2088) := by
  rw [SparsePolynomial.eval_scale, eval_atom2088]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2089 : SparsePolynomial.Poly := [([9,16,17], 1)]
theorem eval_atom2089 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2089 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom2089, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2089_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (199718571175200 : Int) atom2089) := by
  rw [SparsePolynomial.eval_scale, eval_atom2089]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2090 : SparsePolynomial.Poly := [([9,16,18], 1)]
theorem eval_atom2090 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2090 = ((g 9) * (g 16) * (g 18)) := by
  norm_num [atom2090, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2090_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (200900798383248 : Int) atom2090) := by
  rw [SparsePolynomial.eval_scale, eval_atom2090]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2091 : SparsePolynomial.Poly := [([9,16,19], 1)]
theorem eval_atom2091 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2091 = ((g 9) * (g 16) * (g 19)) := by
  norm_num [atom2091, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2091_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (215153486599680 : Int) atom2091) := by
  rw [SparsePolynomial.eval_scale, eval_atom2091]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2092 : SparsePolynomial.Poly := [([9,16,20], 1)]
theorem eval_atom2092 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2092 = ((g 9) * (g 16) * (g 20)) := by
  norm_num [atom2092, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2092_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (370247973267312 : Int) atom2092) := by
  rw [SparsePolynomial.eval_scale, eval_atom2092]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2093 : SparsePolynomial.Poly := [([9,16,21], 1)]
theorem eval_atom2093 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2093 = ((g 9) * (g 16) * (g 21)) := by
  norm_num [atom2093, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2093_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (434270175779880 : Int) atom2093) := by
  rw [SparsePolynomial.eval_scale, eval_atom2093]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2094 : SparsePolynomial.Poly := [([9,16,22], 1)]
theorem eval_atom2094 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2094 = ((g 9) * (g 16) * (g 22)) := by
  norm_num [atom2094, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2094_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (426695606746848 : Int) atom2094) := by
  rw [SparsePolynomial.eval_scale, eval_atom2094]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2095 : SparsePolynomial.Poly := [([9,16,23], 1)]
theorem eval_atom2095 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2095 = ((g 9) * (g 16) * (g 23)) := by
  norm_num [atom2095, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2095_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (632428948727100 : Int) atom2095) := by
  rw [SparsePolynomial.eval_scale, eval_atom2095]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2096 : SparsePolynomial.Poly := [([9,17,17], 1)]
theorem eval_atom2096 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2096 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom2096, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2096_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125452066093200 : Int) atom2096) := by
  rw [SparsePolynomial.eval_scale, eval_atom2096]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2097 : SparsePolynomial.Poly := [([9,17,18], 1)]
theorem eval_atom2097 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2097 = ((g 9) * (g 17) * (g 18)) := by
  norm_num [atom2097, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2097_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (244374569916048 : Int) atom2097) := by
  rw [SparsePolynomial.eval_scale, eval_atom2097]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2098 : SparsePolynomial.Poly := [([9,17,19], 1)]
theorem eval_atom2098 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2098 = ((g 9) * (g 17) * (g 19)) := by
  norm_num [atom2098, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2098_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (276662240110080 : Int) atom2098) := by
  rw [SparsePolynomial.eval_scale, eval_atom2098]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2099 : SparsePolynomial.Poly := [([9,17,20], 1)]
theorem eval_atom2099 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2099 = ((g 9) * (g 17) * (g 20)) := by
  norm_num [atom2099, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2099_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (449791708755312 : Int) atom2099) := by
  rw [SparsePolynomial.eval_scale, eval_atom2099]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2100 : SparsePolynomial.Poly := [([9,17,21], 1)]
theorem eval_atom2100 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2100 = ((g 9) * (g 17) * (g 21)) := by
  norm_num [atom2100, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2100_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (527934365968680 : Int) atom2100) := by
  rw [SparsePolynomial.eval_scale, eval_atom2100]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2101 : SparsePolynomial.Poly := [([9,17,22], 1)]
theorem eval_atom2101 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2101 = ((g 9) * (g 17) * (g 22)) := by
  norm_num [atom2101, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2101_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (533356568718048 : Int) atom2101) := by
  rw [SparsePolynomial.eval_scale, eval_atom2101]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2102 : SparsePolynomial.Poly := [([9,17,23], 1)]
theorem eval_atom2102 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2102 = ((g 9) * (g 17) * (g 23)) := by
  norm_num [atom2102, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2102_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (751253101760700 : Int) atom2102) := by
  rw [SparsePolynomial.eval_scale, eval_atom2102]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2103 : SparsePolynomial.Poly := [([9,18,18], 1)]
theorem eval_atom2103 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2103 = ((g 9) * (g 18) * (g 18)) := by
  norm_num [atom2103, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2103_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164172690291456 : Int) atom2103) := by
  rw [SparsePolynomial.eval_scale, eval_atom2103]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2104 : SparsePolynomial.Poly := [([9,18,19], 1)]
theorem eval_atom2104 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2104 = ((g 9) * (g 18) * (g 19)) := by
  norm_num [atom2104, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2104_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (341402349779568 : Int) atom2104) := by
  rw [SparsePolynomial.eval_scale, eval_atom2104]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2105 : SparsePolynomial.Poly := [([9,18,20], 1)]
theorem eval_atom2105 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2105 = ((g 9) * (g 18) * (g 20)) := by
  norm_num [atom2105, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2105_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (565722016653024 : Int) atom2105) := by
  rw [SparsePolynomial.eval_scale, eval_atom2105]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2106 : SparsePolynomial.Poly := [([9,18,21], 1)]
theorem eval_atom2106 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2106 = ((g 9) * (g 18) * (g 21)) := by
  norm_num [atom2106, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2106_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (601102415080728 : Int) atom2106) := by
  rw [SparsePolynomial.eval_scale, eval_atom2106]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2107 : SparsePolynomial.Poly := [([9,18,22], 1)]
theorem eval_atom2107 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2107 = ((g 9) * (g 18) * (g 22)) := by
  norm_num [atom2107, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2107_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (501233644103904 : Int) atom2107) := by
  rw [SparsePolynomial.eval_scale, eval_atom2107]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2108 : SparsePolynomial.Poly := [([9,18,23], 1)]
theorem eval_atom2108 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2108 = ((g 9) * (g 18) * (g 23)) := by
  norm_num [atom2108, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2108_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (739294473362940 : Int) atom2108) := by
  rw [SparsePolynomial.eval_scale, eval_atom2108]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2109 : SparsePolynomial.Poly := [([9,19,19], 1)]
theorem eval_atom2109 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2109 = ((g 9) * (g 19) * (g 19)) := by
  norm_num [atom2109, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2109_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112255485529968 : Int) atom2109) := by
  rw [SparsePolynomial.eval_scale, eval_atom2109]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2110 : SparsePolynomial.Poly := [([9,19,20], 1)]
theorem eval_atom2110 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2110 = ((g 9) * (g 19) * (g 20)) := by
  norm_num [atom2110, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2110_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (421979166878544 : Int) atom2110) := by
  rw [SparsePolynomial.eval_scale, eval_atom2110]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2111 : SparsePolynomial.Poly := [([9,19,21], 1)]
theorem eval_atom2111 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2111 = ((g 9) * (g 19) * (g 21)) := by
  norm_num [atom2111, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2111_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (455795061431688 : Int) atom2111) := by
  rw [SparsePolynomial.eval_scale, eval_atom2111]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2112 : SparsePolynomial.Poly := [([9,19,22], 1)]
theorem eval_atom2112 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2112 = ((g 9) * (g 19) * (g 22)) := by
  norm_num [atom2112, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2112_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (407529927423456 : Int) atom2112) := by
  rw [SparsePolynomial.eval_scale, eval_atom2112]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2113 : SparsePolynomial.Poly := [([9,19,23], 1)]
theorem eval_atom2113 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2113 = ((g 9) * (g 19) * (g 23)) := by
  norm_num [atom2113, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2113_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (491628696997500 : Int) atom2113) := by
  rw [SparsePolynomial.eval_scale, eval_atom2113]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2114 : SparsePolynomial.Poly := [([9,20,20], 1)]
theorem eval_atom2114 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2114 = ((g 9) * (g 20) * (g 20)) := by
  norm_num [atom2114, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2114_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (315170406616032 : Int) atom2114) := by
  rw [SparsePolynomial.eval_scale, eval_atom2114]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2115 : SparsePolynomial.Poly := [([9,20,21], 1)]
theorem eval_atom2115 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2115 = ((g 9) * (g 20) * (g 21)) := by
  norm_num [atom2115, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2115_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (486539955846648 : Int) atom2115) := by
  rw [SparsePolynomial.eval_scale, eval_atom2115]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2116 : SparsePolynomial.Poly := [([9,20,22], 1)]
theorem eval_atom2116 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2116 = ((g 9) * (g 20) * (g 22)) := by
  norm_num [atom2116, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2116_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (399235093045728 : Int) atom2116) := by
  rw [SparsePolynomial.eval_scale, eval_atom2116]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2117 : SparsePolynomial.Poly := [([9,20,23], 1)]
theorem eval_atom2117 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2117 = ((g 9) * (g 20) * (g 23)) := by
  norm_num [atom2117, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2117_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (482565818257596 : Int) atom2117) := by
  rw [SparsePolynomial.eval_scale, eval_atom2117]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2118 : SparsePolynomial.Poly := [([9,21,21], 1)]
theorem eval_atom2118 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2118 = ((g 9) * (g 21) * (g 21)) := by
  norm_num [atom2118, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2118_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110428842839832 : Int) atom2118) := by
  rw [SparsePolynomial.eval_scale, eval_atom2118]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2119 : SparsePolynomial.Poly := [([9,21,22], 1)]
theorem eval_atom2119 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2119 = ((g 9) * (g 21) * (g 22)) := by
  norm_num [atom2119, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2119_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (180543118688352 : Int) atom2119) := by
  rw [SparsePolynomial.eval_scale, eval_atom2119]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2120 : SparsePolynomial.Poly := [([9,21,23], 1)]
theorem eval_atom2120 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2120 = ((g 9) * (g 21) * (g 23)) := by
  norm_num [atom2120, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2120_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (252854208995580 : Int) atom2120) := by
  rw [SparsePolynomial.eval_scale, eval_atom2120]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2121 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom2121 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2121 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom2121, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2121_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5779150700400 : Int) atom2121) := by
  rw [SparsePolynomial.eval_scale, eval_atom2121]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2122 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom2122 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2122 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom2122, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2122_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3083040576000 : Int) atom2122) := by
  rw [SparsePolynomial.eval_scale, eval_atom2122]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2123 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom2123 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2123 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom2123, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2123_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11430505825200 : Int) atom2123) := by
  rw [SparsePolynomial.eval_scale, eval_atom2123]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2124 : SparsePolynomial.Poly := [([10,11,16], 1)]
theorem eval_atom2124 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2124 = ((g 10) * (g 11) * (g 16)) := by
  norm_num [atom2124, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2124_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3083040576000 : Int) atom2124) := by
  rw [SparsePolynomial.eval_scale, eval_atom2124]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2125 : SparsePolynomial.Poly := [([10,11,17], 1)]
theorem eval_atom2125 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2125 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom2125, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2125_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6166081152000 : Int) atom2125) := by
  rw [SparsePolynomial.eval_scale, eval_atom2125]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2126 : SparsePolynomial.Poly := [([10,11,18], 1)]
theorem eval_atom2126 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2126 = ((g 10) * (g 11) * (g 18)) := by
  norm_num [atom2126, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2126_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7827040153152 : Int) atom2126) := by
  rw [SparsePolynomial.eval_scale, eval_atom2126]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2127 : SparsePolynomial.Poly := [([10,11,21], 1)]
theorem eval_atom2127 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2127 = ((g 10) * (g 11) * (g 21)) := by
  norm_num [atom2127, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2127_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48552573484800 : Int) atom2127) := by
  rw [SparsePolynomial.eval_scale, eval_atom2127]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2128 : SparsePolynomial.Poly := [([10,11,22], 1)]
theorem eval_atom2128 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom2128 = ((g 10) * (g 11) * (g 22)) := by
  norm_num [atom2128, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom2128_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93303439004160 : Int) atom2128) := by
  rw [SparsePolynomial.eval_scale, eval_atom2128]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block028 : SparsePolynomial.Poly := [([9,12,15], 38340001576800), ([9,12,16], 44527345077600), ([9,12,17], 50714688578400), ([9,12,18], 73791992737584), ([9,12,19], 44842698616320), ([9,12,20], 125939444689872), ([9,12,21], 151220555232120), ([9,12,22], 246175983184032), ([9,12,23], 354181063490100), ([9,13,13], 34312779824400), ([9,13,14], 62507318781600), ([9,13,15], 65632884055200), ([9,13,16], 71841489904800), ([9,13,17], 78050095754400), ([9,13,18], 101889785997648), ([9,13,19], 86927253684480), ([9,13,20], 183967270491312), ([9,13,21], 210863159270280), ([9,13,22], 315137321329248), ([9,13,23], 431271363530700), ([9,14,14], 53879456307600), ([9,14,15], 104750290260000), ([9,14,16], 109959565716000), ([9,14,17], 115168841172000), ([9,14,18], 126017705320848), ([9,14,19], 127362899458080), ([9,14,20], 231267918963312), ([9,14,21], 269059953741480), ([9,14,22], 363851473030848), ([9,14,23], 482737543249500), ([9,15,15], 79638791878800), ([9,15,16], 149114181031200), ([9,15,17], 152303533351200), ([9,15,18], 172326134536848), ([9,15,19], 173510210004480), ([9,15,20], 315536083923312), ([9,15,21], 367921016349480), ([9,15,22], 406502174209248), ([9,15,23], 524779126458300), ([9,16,16], 101326387654800), ([9,16,17], 199718571175200), ([9,16,18], 200900798383248), ([9,16,19], 215153486599680), ([9,16,20], 370247973267312), ([9,16,21], 434270175779880), ([9,16,22], 426695606746848), ([9,16,23], 632428948727100), ([9,17,17], 125452066093200), ([9,17,18], 244374569916048), ([9,17,19], 276662240110080), ([9,17,20], 449791708755312), ([9,17,21], 527934365968680), ([9,17,22], 533356568718048), ([9,17,23], 751253101760700), ([9,18,18], 164172690291456), ([9,18,19], 341402349779568), ([9,18,20], 565722016653024), ([9,18,21], 601102415080728), ([9,18,22], 501233644103904), ([9,18,23], 739294473362940), ([9,19,19], 112255485529968), ([9,19,20], 421979166878544), ([9,19,21], 455795061431688), ([9,19,22], 407529927423456), ([9,19,23], 491628696997500), ([9,20,20], 315170406616032), ([9,20,21], 486539955846648), ([9,20,22], 399235093045728), ([9,20,23], 482565818257596), ([9,21,21], 110428842839832), ([9,21,22], 180543118688352), ([9,21,23], 252854208995580), ([10,10,10], 5779150700400), ([10,10,11], 3083040576000), ([10,11,11], 11430505825200), ([10,11,16], 3083040576000), ([10,11,17], 6166081152000), ([10,11,18], 7827040153152), ([10,11,21], 48552573484800), ([10,11,22], 93303439004160)]
theorem block028_data : block028 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38340001576800 : Int) atom2049) (SparsePolynomial.scale (44527345077600 : Int) atom2050)) (SparsePolynomial.merge (SparsePolynomial.scale (50714688578400 : Int) atom2051) (SparsePolynomial.merge (SparsePolynomial.scale (73791992737584 : Int) atom2052) (SparsePolynomial.scale (44842698616320 : Int) atom2053)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (125939444689872 : Int) atom2054) (SparsePolynomial.scale (151220555232120 : Int) atom2055)) (SparsePolynomial.merge (SparsePolynomial.scale (246175983184032 : Int) atom2056) (SparsePolynomial.merge (SparsePolynomial.scale (354181063490100 : Int) atom2057) (SparsePolynomial.scale (34312779824400 : Int) atom2058))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62507318781600 : Int) atom2059) (SparsePolynomial.scale (65632884055200 : Int) atom2060)) (SparsePolynomial.merge (SparsePolynomial.scale (71841489904800 : Int) atom2061) (SparsePolynomial.merge (SparsePolynomial.scale (78050095754400 : Int) atom2062) (SparsePolynomial.scale (101889785997648 : Int) atom2063)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (86927253684480 : Int) atom2064) (SparsePolynomial.scale (183967270491312 : Int) atom2065)) (SparsePolynomial.merge (SparsePolynomial.scale (210863159270280 : Int) atom2066) (SparsePolynomial.merge (SparsePolynomial.scale (315137321329248 : Int) atom2067) (SparsePolynomial.scale (431271363530700 : Int) atom2068)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (53879456307600 : Int) atom2069) (SparsePolynomial.scale (104750290260000 : Int) atom2070)) (SparsePolynomial.merge (SparsePolynomial.scale (109959565716000 : Int) atom2071) (SparsePolynomial.merge (SparsePolynomial.scale (115168841172000 : Int) atom2072) (SparsePolynomial.scale (126017705320848 : Int) atom2073)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (127362899458080 : Int) atom2074) (SparsePolynomial.scale (231267918963312 : Int) atom2075)) (SparsePolynomial.merge (SparsePolynomial.scale (269059953741480 : Int) atom2076) (SparsePolynomial.merge (SparsePolynomial.scale (363851473030848 : Int) atom2077) (SparsePolynomial.scale (482737543249500 : Int) atom2078))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (79638791878800 : Int) atom2079) (SparsePolynomial.scale (149114181031200 : Int) atom2080)) (SparsePolynomial.merge (SparsePolynomial.scale (152303533351200 : Int) atom2081) (SparsePolynomial.merge (SparsePolynomial.scale (172326134536848 : Int) atom2082) (SparsePolynomial.scale (173510210004480 : Int) atom2083)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (315536083923312 : Int) atom2084) (SparsePolynomial.scale (367921016349480 : Int) atom2085)) (SparsePolynomial.merge (SparsePolynomial.scale (406502174209248 : Int) atom2086) (SparsePolynomial.merge (SparsePolynomial.scale (524779126458300 : Int) atom2087) (SparsePolynomial.scale (101326387654800 : Int) atom2088))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (199718571175200 : Int) atom2089) (SparsePolynomial.scale (200900798383248 : Int) atom2090)) (SparsePolynomial.merge (SparsePolynomial.scale (215153486599680 : Int) atom2091) (SparsePolynomial.merge (SparsePolynomial.scale (370247973267312 : Int) atom2092) (SparsePolynomial.scale (434270175779880 : Int) atom2093)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (426695606746848 : Int) atom2094) (SparsePolynomial.scale (632428948727100 : Int) atom2095)) (SparsePolynomial.merge (SparsePolynomial.scale (125452066093200 : Int) atom2096) (SparsePolynomial.merge (SparsePolynomial.scale (244374569916048 : Int) atom2097) (SparsePolynomial.scale (276662240110080 : Int) atom2098))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (449791708755312 : Int) atom2099) (SparsePolynomial.scale (527934365968680 : Int) atom2100)) (SparsePolynomial.merge (SparsePolynomial.scale (533356568718048 : Int) atom2101) (SparsePolynomial.merge (SparsePolynomial.scale (751253101760700 : Int) atom2102) (SparsePolynomial.scale (164172690291456 : Int) atom2103)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (341402349779568 : Int) atom2104) (SparsePolynomial.scale (565722016653024 : Int) atom2105)) (SparsePolynomial.merge (SparsePolynomial.scale (601102415080728 : Int) atom2106) (SparsePolynomial.merge (SparsePolynomial.scale (501233644103904 : Int) atom2107) (SparsePolynomial.scale (739294473362940 : Int) atom2108)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (112255485529968 : Int) atom2109) (SparsePolynomial.scale (421979166878544 : Int) atom2110)) (SparsePolynomial.merge (SparsePolynomial.scale (455795061431688 : Int) atom2111) (SparsePolynomial.merge (SparsePolynomial.scale (407529927423456 : Int) atom2112) (SparsePolynomial.scale (491628696997500 : Int) atom2113)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (315170406616032 : Int) atom2114) (SparsePolynomial.scale (486539955846648 : Int) atom2115)) (SparsePolynomial.merge (SparsePolynomial.scale (399235093045728 : Int) atom2116) (SparsePolynomial.merge (SparsePolynomial.scale (482565818257596 : Int) atom2117) (SparsePolynomial.scale (110428842839832 : Int) atom2118))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (180543118688352 : Int) atom2119) (SparsePolynomial.scale (252854208995580 : Int) atom2120)) (SparsePolynomial.merge (SparsePolynomial.scale (5779150700400 : Int) atom2121) (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2122) (SparsePolynomial.scale (11430505825200 : Int) atom2123)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3083040576000 : Int) atom2124) (SparsePolynomial.scale (6166081152000 : Int) atom2125)) (SparsePolynomial.merge (SparsePolynomial.scale (7827040153152 : Int) atom2126) (SparsePolynomial.merge (SparsePolynomial.scale (48552573484800 : Int) atom2127) (SparsePolynomial.scale (93303439004160 : Int) atom2128)))))))) := by decide +kernel
theorem block028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block028 := by
  rw [block028_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2049_nonneg g hg hA hB) (atom2050_nonneg g hg hA hB)) (add_nonneg (atom2051_nonneg g hg hA hB) (add_nonneg (atom2052_nonneg g hg hA hB) (atom2053_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2054_nonneg g hg hA hB) (atom2055_nonneg g hg hA hB)) (add_nonneg (atom2056_nonneg g hg hA hB) (add_nonneg (atom2057_nonneg g hg hA hB) (atom2058_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2059_nonneg g hg hA hB) (atom2060_nonneg g hg hA hB)) (add_nonneg (atom2061_nonneg g hg hA hB) (add_nonneg (atom2062_nonneg g hg hA hB) (atom2063_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2064_nonneg g hg hA hB) (atom2065_nonneg g hg hA hB)) (add_nonneg (atom2066_nonneg g hg hA hB) (add_nonneg (atom2067_nonneg g hg hA hB) (atom2068_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2069_nonneg g hg hA hB) (atom2070_nonneg g hg hA hB)) (add_nonneg (atom2071_nonneg g hg hA hB) (add_nonneg (atom2072_nonneg g hg hA hB) (atom2073_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2074_nonneg g hg hA hB) (atom2075_nonneg g hg hA hB)) (add_nonneg (atom2076_nonneg g hg hA hB) (add_nonneg (atom2077_nonneg g hg hA hB) (atom2078_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2079_nonneg g hg hA hB) (atom2080_nonneg g hg hA hB)) (add_nonneg (atom2081_nonneg g hg hA hB) (add_nonneg (atom2082_nonneg g hg hA hB) (atom2083_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2084_nonneg g hg hA hB) (atom2085_nonneg g hg hA hB)) (add_nonneg (atom2086_nonneg g hg hA hB) (add_nonneg (atom2087_nonneg g hg hA hB) (atom2088_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2089_nonneg g hg hA hB) (atom2090_nonneg g hg hA hB)) (add_nonneg (atom2091_nonneg g hg hA hB) (add_nonneg (atom2092_nonneg g hg hA hB) (atom2093_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2094_nonneg g hg hA hB) (atom2095_nonneg g hg hA hB)) (add_nonneg (atom2096_nonneg g hg hA hB) (add_nonneg (atom2097_nonneg g hg hA hB) (atom2098_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2099_nonneg g hg hA hB) (atom2100_nonneg g hg hA hB)) (add_nonneg (atom2101_nonneg g hg hA hB) (add_nonneg (atom2102_nonneg g hg hA hB) (atom2103_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2104_nonneg g hg hA hB) (atom2105_nonneg g hg hA hB)) (add_nonneg (atom2106_nonneg g hg hA hB) (add_nonneg (atom2107_nonneg g hg hA hB) (atom2108_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2109_nonneg g hg hA hB) (atom2110_nonneg g hg hA hB)) (add_nonneg (atom2111_nonneg g hg hA hB) (add_nonneg (atom2112_nonneg g hg hA hB) (atom2113_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2114_nonneg g hg hA hB) (atom2115_nonneg g hg hA hB)) (add_nonneg (atom2116_nonneg g hg hA hB) (add_nonneg (atom2117_nonneg g hg hA hB) (atom2118_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2119_nonneg g hg hA hB) (atom2120_nonneg g hg hA hB)) (add_nonneg (atom2121_nonneg g hg hA hB) (add_nonneg (atom2122_nonneg g hg hA hB) (atom2123_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2124_nonneg g hg hA hB) (atom2125_nonneg g hg hA hB)) (add_nonneg (atom2126_nonneg g hg hA hB) (add_nonneg (atom2127_nonneg g hg hA hB) (atom2128_nonneg g hg hA hB))))))))

end APPT.Finite24
