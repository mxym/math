import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2049 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2049 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2049 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom2049, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2049_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38340001576800 : Int) atom2049) := by
  rw [SparsePolynomial.eval_scale, eval_atom2049]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2049Coded : CoefficientMerge.Poly := [(nat_lit 5487, Int.ofNat (nat_lit 1))]
theorem atom2049Coded_decode : atom2049 = SparsePolynomial.decodeCubic 24 atom2049Coded := by decide +kernel
theorem atom2049Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (38340001576800 : Int) atom2049Coded) := by
  have h := atom2049_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2049Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2050 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2050 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2050 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom2050, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2050_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44527345077600 : Int) atom2050) := by
  rw [SparsePolynomial.eval_scale, eval_atom2050]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2050Coded : CoefficientMerge.Poly := [(nat_lit 5488, Int.ofNat (nat_lit 1))]
theorem atom2050Coded_decode : atom2050 = SparsePolynomial.decodeCubic 24 atom2050Coded := by decide +kernel
theorem atom2050Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (44527345077600 : Int) atom2050Coded) := by
  have h := atom2050_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2050Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2051 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2051 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2051 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom2051, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2051_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50714688578400 : Int) atom2051) := by
  rw [SparsePolynomial.eval_scale, eval_atom2051]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2051Coded : CoefficientMerge.Poly := [(nat_lit 5489, Int.ofNat (nat_lit 1))]
theorem atom2051Coded_decode : atom2051 = SparsePolynomial.decodeCubic 24 atom2051Coded := by decide +kernel
theorem atom2051Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (50714688578400 : Int) atom2051Coded) := by
  have h := atom2051_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2051Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2052 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2052 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2052 = ((g 9) * (g 12) * (g 18)) := by
  norm_num [atom2052, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2052_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73791992737584 : Int) atom2052) := by
  rw [SparsePolynomial.eval_scale, eval_atom2052]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2052Coded : CoefficientMerge.Poly := [(nat_lit 5490, Int.ofNat (nat_lit 1))]
theorem atom2052Coded_decode : atom2052 = SparsePolynomial.decodeCubic 24 atom2052Coded := by decide +kernel
theorem atom2052Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73791992737584 : Int) atom2052Coded) := by
  have h := atom2052_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2052Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2053 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2053 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2053 = ((g 9) * (g 12) * (g 19)) := by
  norm_num [atom2053, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2053_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44842698616320 : Int) atom2053) := by
  rw [SparsePolynomial.eval_scale, eval_atom2053]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2053Coded : CoefficientMerge.Poly := [(nat_lit 5491, Int.ofNat (nat_lit 1))]
theorem atom2053Coded_decode : atom2053 = SparsePolynomial.decodeCubic 24 atom2053Coded := by decide +kernel
theorem atom2053Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (44842698616320 : Int) atom2053Coded) := by
  have h := atom2053_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2053Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2054 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2054 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2054 = ((g 9) * (g 12) * (g 20)) := by
  norm_num [atom2054, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2054_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125939444689872 : Int) atom2054) := by
  rw [SparsePolynomial.eval_scale, eval_atom2054]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2054Coded : CoefficientMerge.Poly := [(nat_lit 5492, Int.ofNat (nat_lit 1))]
theorem atom2054Coded_decode : atom2054 = SparsePolynomial.decodeCubic 24 atom2054Coded := by decide +kernel
theorem atom2054Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125939444689872 : Int) atom2054Coded) := by
  have h := atom2054_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2054Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2055 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2055 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2055 = ((g 9) * (g 12) * (g 21)) := by
  norm_num [atom2055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2055_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151220555232120 : Int) atom2055) := by
  rw [SparsePolynomial.eval_scale, eval_atom2055]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2055Coded : CoefficientMerge.Poly := [(nat_lit 5493, Int.ofNat (nat_lit 1))]
theorem atom2055Coded_decode : atom2055 = SparsePolynomial.decodeCubic 24 atom2055Coded := by decide +kernel
theorem atom2055Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151220555232120 : Int) atom2055Coded) := by
  have h := atom2055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2056 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2056 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2056 = ((g 9) * (g 12) * (g 22)) := by
  norm_num [atom2056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2056_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (246175983184032 : Int) atom2056) := by
  rw [SparsePolynomial.eval_scale, eval_atom2056]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2056Coded : CoefficientMerge.Poly := [(nat_lit 5494, Int.ofNat (nat_lit 1))]
theorem atom2056Coded_decode : atom2056 = SparsePolynomial.decodeCubic 24 atom2056Coded := by decide +kernel
theorem atom2056Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (246175983184032 : Int) atom2056Coded) := by
  have h := atom2056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2057 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2057 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2057 = ((g 9) * (g 12) * (g 23)) := by
  norm_num [atom2057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2057_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (354181063490100 : Int) atom2057) := by
  rw [SparsePolynomial.eval_scale, eval_atom2057]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2057Coded : CoefficientMerge.Poly := [(nat_lit 5495, Int.ofNat (nat_lit 1))]
theorem atom2057Coded_decode : atom2057 = SparsePolynomial.decodeCubic 24 atom2057Coded := by decide +kernel
theorem atom2057Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (354181063490100 : Int) atom2057Coded) := by
  have h := atom2057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2058 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2058 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2058 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom2058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2058_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34312779824400 : Int) atom2058) := by
  rw [SparsePolynomial.eval_scale, eval_atom2058]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2058Coded : CoefficientMerge.Poly := [(nat_lit 5509, Int.ofNat (nat_lit 1))]
theorem atom2058Coded_decode : atom2058 = SparsePolynomial.decodeCubic 24 atom2058Coded := by decide +kernel
theorem atom2058Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34312779824400 : Int) atom2058Coded) := by
  have h := atom2058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2059 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2059 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2059 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom2059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2059_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62507318781600 : Int) atom2059) := by
  rw [SparsePolynomial.eval_scale, eval_atom2059]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2059Coded : CoefficientMerge.Poly := [(nat_lit 5510, Int.ofNat (nat_lit 1))]
theorem atom2059Coded_decode : atom2059 = SparsePolynomial.decodeCubic 24 atom2059Coded := by decide +kernel
theorem atom2059Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62507318781600 : Int) atom2059Coded) := by
  have h := atom2059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2060 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2060 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2060 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom2060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2060_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65632884055200 : Int) atom2060) := by
  rw [SparsePolynomial.eval_scale, eval_atom2060]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2060Coded : CoefficientMerge.Poly := [(nat_lit 5511, Int.ofNat (nat_lit 1))]
theorem atom2060Coded_decode : atom2060 = SparsePolynomial.decodeCubic 24 atom2060Coded := by decide +kernel
theorem atom2060Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65632884055200 : Int) atom2060Coded) := by
  have h := atom2060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2061 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2061 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2061 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom2061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2061_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71841489904800 : Int) atom2061) := by
  rw [SparsePolynomial.eval_scale, eval_atom2061]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2061Coded : CoefficientMerge.Poly := [(nat_lit 5512, Int.ofNat (nat_lit 1))]
theorem atom2061Coded_decode : atom2061 = SparsePolynomial.decodeCubic 24 atom2061Coded := by decide +kernel
theorem atom2061Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71841489904800 : Int) atom2061Coded) := by
  have h := atom2061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2062 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2062 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2062 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom2062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2062_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78050095754400 : Int) atom2062) := by
  rw [SparsePolynomial.eval_scale, eval_atom2062]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2062Coded : CoefficientMerge.Poly := [(nat_lit 5513, Int.ofNat (nat_lit 1))]
theorem atom2062Coded_decode : atom2062 = SparsePolynomial.decodeCubic 24 atom2062Coded := by decide +kernel
theorem atom2062Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78050095754400 : Int) atom2062Coded) := by
  have h := atom2062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2063 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2063 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2063 = ((g 9) * (g 13) * (g 18)) := by
  norm_num [atom2063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2063_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101889785997648 : Int) atom2063) := by
  rw [SparsePolynomial.eval_scale, eval_atom2063]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2063Coded : CoefficientMerge.Poly := [(nat_lit 5514, Int.ofNat (nat_lit 1))]
theorem atom2063Coded_decode : atom2063 = SparsePolynomial.decodeCubic 24 atom2063Coded := by decide +kernel
theorem atom2063Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101889785997648 : Int) atom2063Coded) := by
  have h := atom2063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2064 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2064 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2064 = ((g 9) * (g 13) * (g 19)) := by
  norm_num [atom2064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2064_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86927253684480 : Int) atom2064) := by
  rw [SparsePolynomial.eval_scale, eval_atom2064]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2064Coded : CoefficientMerge.Poly := [(nat_lit 5515, Int.ofNat (nat_lit 1))]
theorem atom2064Coded_decode : atom2064 = SparsePolynomial.decodeCubic 24 atom2064Coded := by decide +kernel
theorem atom2064Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (86927253684480 : Int) atom2064Coded) := by
  have h := atom2064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2065 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2065 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2065 = ((g 9) * (g 13) * (g 20)) := by
  norm_num [atom2065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2065_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183967270491312 : Int) atom2065) := by
  rw [SparsePolynomial.eval_scale, eval_atom2065]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2065Coded : CoefficientMerge.Poly := [(nat_lit 5516, Int.ofNat (nat_lit 1))]
theorem atom2065Coded_decode : atom2065 = SparsePolynomial.decodeCubic 24 atom2065Coded := by decide +kernel
theorem atom2065Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183967270491312 : Int) atom2065Coded) := by
  have h := atom2065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2066 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2066 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2066 = ((g 9) * (g 13) * (g 21)) := by
  norm_num [atom2066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2066_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210863159270280 : Int) atom2066) := by
  rw [SparsePolynomial.eval_scale, eval_atom2066]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2066Coded : CoefficientMerge.Poly := [(nat_lit 5517, Int.ofNat (nat_lit 1))]
theorem atom2066Coded_decode : atom2066 = SparsePolynomial.decodeCubic 24 atom2066Coded := by decide +kernel
theorem atom2066Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210863159270280 : Int) atom2066Coded) := by
  have h := atom2066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2067 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2067 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2067 = ((g 9) * (g 13) * (g 22)) := by
  norm_num [atom2067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2067_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315137321329248 : Int) atom2067) := by
  rw [SparsePolynomial.eval_scale, eval_atom2067]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2067Coded : CoefficientMerge.Poly := [(nat_lit 5518, Int.ofNat (nat_lit 1))]
theorem atom2067Coded_decode : atom2067 = SparsePolynomial.decodeCubic 24 atom2067Coded := by decide +kernel
theorem atom2067Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315137321329248 : Int) atom2067Coded) := by
  have h := atom2067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2068 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2068 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2068 = ((g 9) * (g 13) * (g 23)) := by
  norm_num [atom2068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2068_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431271363530700 : Int) atom2068) := by
  rw [SparsePolynomial.eval_scale, eval_atom2068]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2068Coded : CoefficientMerge.Poly := [(nat_lit 5519, Int.ofNat (nat_lit 1))]
theorem atom2068Coded_decode : atom2068 = SparsePolynomial.decodeCubic 24 atom2068Coded := by decide +kernel
theorem atom2068Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (431271363530700 : Int) atom2068Coded) := by
  have h := atom2068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2069 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2069 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2069 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom2069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2069_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53879456307600 : Int) atom2069) := by
  rw [SparsePolynomial.eval_scale, eval_atom2069]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2069Coded : CoefficientMerge.Poly := [(nat_lit 5534, Int.ofNat (nat_lit 1))]
theorem atom2069Coded_decode : atom2069 = SparsePolynomial.decodeCubic 24 atom2069Coded := by decide +kernel
theorem atom2069Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53879456307600 : Int) atom2069Coded) := by
  have h := atom2069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2070 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2070 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2070 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom2070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2070_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104750290260000 : Int) atom2070) := by
  rw [SparsePolynomial.eval_scale, eval_atom2070]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2070Coded : CoefficientMerge.Poly := [(nat_lit 5535, Int.ofNat (nat_lit 1))]
theorem atom2070Coded_decode : atom2070 = SparsePolynomial.decodeCubic 24 atom2070Coded := by decide +kernel
theorem atom2070Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104750290260000 : Int) atom2070Coded) := by
  have h := atom2070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2071 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2071 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2071 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom2071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2071_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109959565716000 : Int) atom2071) := by
  rw [SparsePolynomial.eval_scale, eval_atom2071]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2071Coded : CoefficientMerge.Poly := [(nat_lit 5536, Int.ofNat (nat_lit 1))]
theorem atom2071Coded_decode : atom2071 = SparsePolynomial.decodeCubic 24 atom2071Coded := by decide +kernel
theorem atom2071Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109959565716000 : Int) atom2071Coded) := by
  have h := atom2071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2072 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2072 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2072 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom2072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2072_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115168841172000 : Int) atom2072) := by
  rw [SparsePolynomial.eval_scale, eval_atom2072]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2072Coded : CoefficientMerge.Poly := [(nat_lit 5537, Int.ofNat (nat_lit 1))]
theorem atom2072Coded_decode : atom2072 = SparsePolynomial.decodeCubic 24 atom2072Coded := by decide +kernel
theorem atom2072Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (115168841172000 : Int) atom2072Coded) := by
  have h := atom2072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2073 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2073 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2073 = ((g 9) * (g 14) * (g 18)) := by
  norm_num [atom2073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2073_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126017705320848 : Int) atom2073) := by
  rw [SparsePolynomial.eval_scale, eval_atom2073]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2073Coded : CoefficientMerge.Poly := [(nat_lit 5538, Int.ofNat (nat_lit 1))]
theorem atom2073Coded_decode : atom2073 = SparsePolynomial.decodeCubic 24 atom2073Coded := by decide +kernel
theorem atom2073Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126017705320848 : Int) atom2073Coded) := by
  have h := atom2073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2074 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2074 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2074 = ((g 9) * (g 14) * (g 19)) := by
  norm_num [atom2074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2074_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127362899458080 : Int) atom2074) := by
  rw [SparsePolynomial.eval_scale, eval_atom2074]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2074Coded : CoefficientMerge.Poly := [(nat_lit 5539, Int.ofNat (nat_lit 1))]
theorem atom2074Coded_decode : atom2074 = SparsePolynomial.decodeCubic 24 atom2074Coded := by decide +kernel
theorem atom2074Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (127362899458080 : Int) atom2074Coded) := by
  have h := atom2074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2075 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2075 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2075 = ((g 9) * (g 14) * (g 20)) := by
  norm_num [atom2075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2075_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231267918963312 : Int) atom2075) := by
  rw [SparsePolynomial.eval_scale, eval_atom2075]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2075Coded : CoefficientMerge.Poly := [(nat_lit 5540, Int.ofNat (nat_lit 1))]
theorem atom2075Coded_decode : atom2075 = SparsePolynomial.decodeCubic 24 atom2075Coded := by decide +kernel
theorem atom2075Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231267918963312 : Int) atom2075Coded) := by
  have h := atom2075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2076 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2076 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2076 = ((g 9) * (g 14) * (g 21)) := by
  norm_num [atom2076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2076_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269059953741480 : Int) atom2076) := by
  rw [SparsePolynomial.eval_scale, eval_atom2076]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2076Coded : CoefficientMerge.Poly := [(nat_lit 5541, Int.ofNat (nat_lit 1))]
theorem atom2076Coded_decode : atom2076 = SparsePolynomial.decodeCubic 24 atom2076Coded := by decide +kernel
theorem atom2076Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269059953741480 : Int) atom2076Coded) := by
  have h := atom2076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2077 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2077 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2077 = ((g 9) * (g 14) * (g 22)) := by
  norm_num [atom2077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2077_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (363851473030848 : Int) atom2077) := by
  rw [SparsePolynomial.eval_scale, eval_atom2077]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2077Coded : CoefficientMerge.Poly := [(nat_lit 5542, Int.ofNat (nat_lit 1))]
theorem atom2077Coded_decode : atom2077 = SparsePolynomial.decodeCubic 24 atom2077Coded := by decide +kernel
theorem atom2077Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (363851473030848 : Int) atom2077Coded) := by
  have h := atom2077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2078 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2078 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2078 = ((g 9) * (g 14) * (g 23)) := by
  norm_num [atom2078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2078_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482737543249500 : Int) atom2078) := by
  rw [SparsePolynomial.eval_scale, eval_atom2078]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2078Coded : CoefficientMerge.Poly := [(nat_lit 5543, Int.ofNat (nat_lit 1))]
theorem atom2078Coded_decode : atom2078 = SparsePolynomial.decodeCubic 24 atom2078Coded := by decide +kernel
theorem atom2078Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482737543249500 : Int) atom2078Coded) := by
  have h := atom2078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2079 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2079 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2079 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom2079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2079_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79638791878800 : Int) atom2079) := by
  rw [SparsePolynomial.eval_scale, eval_atom2079]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2079Coded : CoefficientMerge.Poly := [(nat_lit 5559, Int.ofNat (nat_lit 1))]
theorem atom2079Coded_decode : atom2079 = SparsePolynomial.decodeCubic 24 atom2079Coded := by decide +kernel
theorem atom2079Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79638791878800 : Int) atom2079Coded) := by
  have h := atom2079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2080 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2080 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2080 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom2080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2080_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149114181031200 : Int) atom2080) := by
  rw [SparsePolynomial.eval_scale, eval_atom2080]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2080Coded : CoefficientMerge.Poly := [(nat_lit 5560, Int.ofNat (nat_lit 1))]
theorem atom2080Coded_decode : atom2080 = SparsePolynomial.decodeCubic 24 atom2080Coded := by decide +kernel
theorem atom2080Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149114181031200 : Int) atom2080Coded) := by
  have h := atom2080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2081 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2081 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2081 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom2081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2081_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152303533351200 : Int) atom2081) := by
  rw [SparsePolynomial.eval_scale, eval_atom2081]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2081Coded : CoefficientMerge.Poly := [(nat_lit 5561, Int.ofNat (nat_lit 1))]
theorem atom2081Coded_decode : atom2081 = SparsePolynomial.decodeCubic 24 atom2081Coded := by decide +kernel
theorem atom2081Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152303533351200 : Int) atom2081Coded) := by
  have h := atom2081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2082 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2082 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2082 = ((g 9) * (g 15) * (g 18)) := by
  norm_num [atom2082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2082_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172326134536848 : Int) atom2082) := by
  rw [SparsePolynomial.eval_scale, eval_atom2082]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2082Coded : CoefficientMerge.Poly := [(nat_lit 5562, Int.ofNat (nat_lit 1))]
theorem atom2082Coded_decode : atom2082 = SparsePolynomial.decodeCubic 24 atom2082Coded := by decide +kernel
theorem atom2082Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (172326134536848 : Int) atom2082Coded) := by
  have h := atom2082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2083 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2083 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2083 = ((g 9) * (g 15) * (g 19)) := by
  norm_num [atom2083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2083_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173510210004480 : Int) atom2083) := by
  rw [SparsePolynomial.eval_scale, eval_atom2083]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2083Coded : CoefficientMerge.Poly := [(nat_lit 5563, Int.ofNat (nat_lit 1))]
theorem atom2083Coded_decode : atom2083 = SparsePolynomial.decodeCubic 24 atom2083Coded := by decide +kernel
theorem atom2083Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (173510210004480 : Int) atom2083Coded) := by
  have h := atom2083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2084 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2084 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2084 = ((g 9) * (g 15) * (g 20)) := by
  norm_num [atom2084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2084_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315536083923312 : Int) atom2084) := by
  rw [SparsePolynomial.eval_scale, eval_atom2084]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2084Coded : CoefficientMerge.Poly := [(nat_lit 5564, Int.ofNat (nat_lit 1))]
theorem atom2084Coded_decode : atom2084 = SparsePolynomial.decodeCubic 24 atom2084Coded := by decide +kernel
theorem atom2084Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315536083923312 : Int) atom2084Coded) := by
  have h := atom2084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2085 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2085 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2085 = ((g 9) * (g 15) * (g 21)) := by
  norm_num [atom2085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2085_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (367921016349480 : Int) atom2085) := by
  rw [SparsePolynomial.eval_scale, eval_atom2085]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2085Coded : CoefficientMerge.Poly := [(nat_lit 5565, Int.ofNat (nat_lit 1))]
theorem atom2085Coded_decode : atom2085 = SparsePolynomial.decodeCubic 24 atom2085Coded := by decide +kernel
theorem atom2085Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (367921016349480 : Int) atom2085Coded) := by
  have h := atom2085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2086 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2086 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2086 = ((g 9) * (g 15) * (g 22)) := by
  norm_num [atom2086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2086_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (406502174209248 : Int) atom2086) := by
  rw [SparsePolynomial.eval_scale, eval_atom2086]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2086Coded : CoefficientMerge.Poly := [(nat_lit 5566, Int.ofNat (nat_lit 1))]
theorem atom2086Coded_decode : atom2086 = SparsePolynomial.decodeCubic 24 atom2086Coded := by decide +kernel
theorem atom2086Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (406502174209248 : Int) atom2086Coded) := by
  have h := atom2086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2087 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2087 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2087 = ((g 9) * (g 15) * (g 23)) := by
  norm_num [atom2087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2087_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524779126458300 : Int) atom2087) := by
  rw [SparsePolynomial.eval_scale, eval_atom2087]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2087Coded : CoefficientMerge.Poly := [(nat_lit 5567, Int.ofNat (nat_lit 1))]
theorem atom2087Coded_decode : atom2087 = SparsePolynomial.decodeCubic 24 atom2087Coded := by decide +kernel
theorem atom2087Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (524779126458300 : Int) atom2087Coded) := by
  have h := atom2087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2088 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2088 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2088 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom2088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2088_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101326387654800 : Int) atom2088) := by
  rw [SparsePolynomial.eval_scale, eval_atom2088]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2088Coded : CoefficientMerge.Poly := [(nat_lit 5584, Int.ofNat (nat_lit 1))]
theorem atom2088Coded_decode : atom2088 = SparsePolynomial.decodeCubic 24 atom2088Coded := by decide +kernel
theorem atom2088Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101326387654800 : Int) atom2088Coded) := by
  have h := atom2088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2089 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2089 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2089 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom2089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2089_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199718571175200 : Int) atom2089) := by
  rw [SparsePolynomial.eval_scale, eval_atom2089]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2089Coded : CoefficientMerge.Poly := [(nat_lit 5585, Int.ofNat (nat_lit 1))]
theorem atom2089Coded_decode : atom2089 = SparsePolynomial.decodeCubic 24 atom2089Coded := by decide +kernel
theorem atom2089Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (199718571175200 : Int) atom2089Coded) := by
  have h := atom2089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2090 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2090 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2090 = ((g 9) * (g 16) * (g 18)) := by
  norm_num [atom2090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2090_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (200900798383248 : Int) atom2090) := by
  rw [SparsePolynomial.eval_scale, eval_atom2090]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2090Coded : CoefficientMerge.Poly := [(nat_lit 5586, Int.ofNat (nat_lit 1))]
theorem atom2090Coded_decode : atom2090 = SparsePolynomial.decodeCubic 24 atom2090Coded := by decide +kernel
theorem atom2090Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (200900798383248 : Int) atom2090Coded) := by
  have h := atom2090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2091 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2091 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2091 = ((g 9) * (g 16) * (g 19)) := by
  norm_num [atom2091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2091_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215153486599680 : Int) atom2091) := by
  rw [SparsePolynomial.eval_scale, eval_atom2091]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2091Coded : CoefficientMerge.Poly := [(nat_lit 5587, Int.ofNat (nat_lit 1))]
theorem atom2091Coded_decode : atom2091 = SparsePolynomial.decodeCubic 24 atom2091Coded := by decide +kernel
theorem atom2091Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215153486599680 : Int) atom2091Coded) := by
  have h := atom2091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2092 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2092 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2092 = ((g 9) * (g 16) * (g 20)) := by
  norm_num [atom2092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2092_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370247973267312 : Int) atom2092) := by
  rw [SparsePolynomial.eval_scale, eval_atom2092]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2092Coded : CoefficientMerge.Poly := [(nat_lit 5588, Int.ofNat (nat_lit 1))]
theorem atom2092Coded_decode : atom2092 = SparsePolynomial.decodeCubic 24 atom2092Coded := by decide +kernel
theorem atom2092Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (370247973267312 : Int) atom2092Coded) := by
  have h := atom2092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2093 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2093 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2093 = ((g 9) * (g 16) * (g 21)) := by
  norm_num [atom2093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2093_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434270175779880 : Int) atom2093) := by
  rw [SparsePolynomial.eval_scale, eval_atom2093]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2093Coded : CoefficientMerge.Poly := [(nat_lit 5589, Int.ofNat (nat_lit 1))]
theorem atom2093Coded_decode : atom2093 = SparsePolynomial.decodeCubic 24 atom2093Coded := by decide +kernel
theorem atom2093Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434270175779880 : Int) atom2093Coded) := by
  have h := atom2093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2094 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2094 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2094 = ((g 9) * (g 16) * (g 22)) := by
  norm_num [atom2094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2094_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426695606746848 : Int) atom2094) := by
  rw [SparsePolynomial.eval_scale, eval_atom2094]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2094Coded : CoefficientMerge.Poly := [(nat_lit 5590, Int.ofNat (nat_lit 1))]
theorem atom2094Coded_decode : atom2094 = SparsePolynomial.decodeCubic 24 atom2094Coded := by decide +kernel
theorem atom2094Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426695606746848 : Int) atom2094Coded) := by
  have h := atom2094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2095 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2095 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2095 = ((g 9) * (g 16) * (g 23)) := by
  norm_num [atom2095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2095_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (632428948727100 : Int) atom2095) := by
  rw [SparsePolynomial.eval_scale, eval_atom2095]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2095Coded : CoefficientMerge.Poly := [(nat_lit 5591, Int.ofNat (nat_lit 1))]
theorem atom2095Coded_decode : atom2095 = SparsePolynomial.decodeCubic 24 atom2095Coded := by decide +kernel
theorem atom2095Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (632428948727100 : Int) atom2095Coded) := by
  have h := atom2095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2096 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2096 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2096 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom2096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2096_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125452066093200 : Int) atom2096) := by
  rw [SparsePolynomial.eval_scale, eval_atom2096]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2096Coded : CoefficientMerge.Poly := [(nat_lit 5609, Int.ofNat (nat_lit 1))]
theorem atom2096Coded_decode : atom2096 = SparsePolynomial.decodeCubic 24 atom2096Coded := by decide +kernel
theorem atom2096Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125452066093200 : Int) atom2096Coded) := by
  have h := atom2096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2097 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2097 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2097 = ((g 9) * (g 17) * (g 18)) := by
  norm_num [atom2097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2097_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244374569916048 : Int) atom2097) := by
  rw [SparsePolynomial.eval_scale, eval_atom2097]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2097Coded : CoefficientMerge.Poly := [(nat_lit 5610, Int.ofNat (nat_lit 1))]
theorem atom2097Coded_decode : atom2097 = SparsePolynomial.decodeCubic 24 atom2097Coded := by decide +kernel
theorem atom2097Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (244374569916048 : Int) atom2097Coded) := by
  have h := atom2097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2098 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2098 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2098 = ((g 9) * (g 17) * (g 19)) := by
  norm_num [atom2098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2098_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276662240110080 : Int) atom2098) := by
  rw [SparsePolynomial.eval_scale, eval_atom2098]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2098Coded : CoefficientMerge.Poly := [(nat_lit 5611, Int.ofNat (nat_lit 1))]
theorem atom2098Coded_decode : atom2098 = SparsePolynomial.decodeCubic 24 atom2098Coded := by decide +kernel
theorem atom2098Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276662240110080 : Int) atom2098Coded) := by
  have h := atom2098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2099 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2099 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2099 = ((g 9) * (g 17) * (g 20)) := by
  norm_num [atom2099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2099_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (449791708755312 : Int) atom2099) := by
  rw [SparsePolynomial.eval_scale, eval_atom2099]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2099Coded : CoefficientMerge.Poly := [(nat_lit 5612, Int.ofNat (nat_lit 1))]
theorem atom2099Coded_decode : atom2099 = SparsePolynomial.decodeCubic 24 atom2099Coded := by decide +kernel
theorem atom2099Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (449791708755312 : Int) atom2099Coded) := by
  have h := atom2099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2100 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2100 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2100 = ((g 9) * (g 17) * (g 21)) := by
  norm_num [atom2100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2100_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (527934365968680 : Int) atom2100) := by
  rw [SparsePolynomial.eval_scale, eval_atom2100]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2100Coded : CoefficientMerge.Poly := [(nat_lit 5613, Int.ofNat (nat_lit 1))]
theorem atom2100Coded_decode : atom2100 = SparsePolynomial.decodeCubic 24 atom2100Coded := by decide +kernel
theorem atom2100Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (527934365968680 : Int) atom2100Coded) := by
  have h := atom2100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2101 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2101 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2101 = ((g 9) * (g 17) * (g 22)) := by
  norm_num [atom2101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2101_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (533356568718048 : Int) atom2101) := by
  rw [SparsePolynomial.eval_scale, eval_atom2101]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2101Coded : CoefficientMerge.Poly := [(nat_lit 5614, Int.ofNat (nat_lit 1))]
theorem atom2101Coded_decode : atom2101 = SparsePolynomial.decodeCubic 24 atom2101Coded := by decide +kernel
theorem atom2101Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (533356568718048 : Int) atom2101Coded) := by
  have h := atom2101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2102 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2102 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2102 = ((g 9) * (g 17) * (g 23)) := by
  norm_num [atom2102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2102_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (751253101760700 : Int) atom2102) := by
  rw [SparsePolynomial.eval_scale, eval_atom2102]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2102Coded : CoefficientMerge.Poly := [(nat_lit 5615, Int.ofNat (nat_lit 1))]
theorem atom2102Coded_decode : atom2102 = SparsePolynomial.decodeCubic 24 atom2102Coded := by decide +kernel
theorem atom2102Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (751253101760700 : Int) atom2102Coded) := by
  have h := atom2102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2103 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2103 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2103 = ((g 9) * (g 18) * (g 18)) := by
  norm_num [atom2103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2103_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164172690291456 : Int) atom2103) := by
  rw [SparsePolynomial.eval_scale, eval_atom2103]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2103Coded : CoefficientMerge.Poly := [(nat_lit 5634, Int.ofNat (nat_lit 1))]
theorem atom2103Coded_decode : atom2103 = SparsePolynomial.decodeCubic 24 atom2103Coded := by decide +kernel
theorem atom2103Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164172690291456 : Int) atom2103Coded) := by
  have h := atom2103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2104 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2104 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2104 = ((g 9) * (g 18) * (g 19)) := by
  norm_num [atom2104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2104_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (341402349779568 : Int) atom2104) := by
  rw [SparsePolynomial.eval_scale, eval_atom2104]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2104Coded : CoefficientMerge.Poly := [(nat_lit 5635, Int.ofNat (nat_lit 1))]
theorem atom2104Coded_decode : atom2104 = SparsePolynomial.decodeCubic 24 atom2104Coded := by decide +kernel
theorem atom2104Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (341402349779568 : Int) atom2104Coded) := by
  have h := atom2104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2105 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2105 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2105 = ((g 9) * (g 18) * (g 20)) := by
  norm_num [atom2105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2105_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (565722016653024 : Int) atom2105) := by
  rw [SparsePolynomial.eval_scale, eval_atom2105]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2105Coded : CoefficientMerge.Poly := [(nat_lit 5636, Int.ofNat (nat_lit 1))]
theorem atom2105Coded_decode : atom2105 = SparsePolynomial.decodeCubic 24 atom2105Coded := by decide +kernel
theorem atom2105Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (565722016653024 : Int) atom2105Coded) := by
  have h := atom2105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2106 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2106 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2106 = ((g 9) * (g 18) * (g 21)) := by
  norm_num [atom2106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2106_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (601102415080728 : Int) atom2106) := by
  rw [SparsePolynomial.eval_scale, eval_atom2106]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2106Coded : CoefficientMerge.Poly := [(nat_lit 5637, Int.ofNat (nat_lit 1))]
theorem atom2106Coded_decode : atom2106 = SparsePolynomial.decodeCubic 24 atom2106Coded := by decide +kernel
theorem atom2106Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (601102415080728 : Int) atom2106Coded) := by
  have h := atom2106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2107 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2107 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2107 = ((g 9) * (g 18) * (g 22)) := by
  norm_num [atom2107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2107_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (501233644103904 : Int) atom2107) := by
  rw [SparsePolynomial.eval_scale, eval_atom2107]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2107Coded : CoefficientMerge.Poly := [(nat_lit 5638, Int.ofNat (nat_lit 1))]
theorem atom2107Coded_decode : atom2107 = SparsePolynomial.decodeCubic 24 atom2107Coded := by decide +kernel
theorem atom2107Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (501233644103904 : Int) atom2107Coded) := by
  have h := atom2107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2108 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2108 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2108 = ((g 9) * (g 18) * (g 23)) := by
  norm_num [atom2108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2108_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (739294473362940 : Int) atom2108) := by
  rw [SparsePolynomial.eval_scale, eval_atom2108]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2108Coded : CoefficientMerge.Poly := [(nat_lit 5639, Int.ofNat (nat_lit 1))]
theorem atom2108Coded_decode : atom2108 = SparsePolynomial.decodeCubic 24 atom2108Coded := by decide +kernel
theorem atom2108Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (739294473362940 : Int) atom2108Coded) := by
  have h := atom2108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2109 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2109 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2109 = ((g 9) * (g 19) * (g 19)) := by
  norm_num [atom2109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2109_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112255485529968 : Int) atom2109) := by
  rw [SparsePolynomial.eval_scale, eval_atom2109]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2109Coded : CoefficientMerge.Poly := [(nat_lit 5659, Int.ofNat (nat_lit 1))]
theorem atom2109Coded_decode : atom2109 = SparsePolynomial.decodeCubic 24 atom2109Coded := by decide +kernel
theorem atom2109Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (112255485529968 : Int) atom2109Coded) := by
  have h := atom2109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2110 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2110 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2110 = ((g 9) * (g 19) * (g 20)) := by
  norm_num [atom2110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2110_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (421979166878544 : Int) atom2110) := by
  rw [SparsePolynomial.eval_scale, eval_atom2110]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2110Coded : CoefficientMerge.Poly := [(nat_lit 5660, Int.ofNat (nat_lit 1))]
theorem atom2110Coded_decode : atom2110 = SparsePolynomial.decodeCubic 24 atom2110Coded := by decide +kernel
theorem atom2110Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (421979166878544 : Int) atom2110Coded) := by
  have h := atom2110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2111 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2111 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2111 = ((g 9) * (g 19) * (g 21)) := by
  norm_num [atom2111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2111_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (455795061431688 : Int) atom2111) := by
  rw [SparsePolynomial.eval_scale, eval_atom2111]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2111Coded : CoefficientMerge.Poly := [(nat_lit 5661, Int.ofNat (nat_lit 1))]
theorem atom2111Coded_decode : atom2111 = SparsePolynomial.decodeCubic 24 atom2111Coded := by decide +kernel
theorem atom2111Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (455795061431688 : Int) atom2111Coded) := by
  have h := atom2111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2112 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2112 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2112 = ((g 9) * (g 19) * (g 22)) := by
  norm_num [atom2112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2112_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407529927423456 : Int) atom2112) := by
  rw [SparsePolynomial.eval_scale, eval_atom2112]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2112Coded : CoefficientMerge.Poly := [(nat_lit 5662, Int.ofNat (nat_lit 1))]
theorem atom2112Coded_decode : atom2112 = SparsePolynomial.decodeCubic 24 atom2112Coded := by decide +kernel
theorem atom2112Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (407529927423456 : Int) atom2112Coded) := by
  have h := atom2112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2113 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2113 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2113 = ((g 9) * (g 19) * (g 23)) := by
  norm_num [atom2113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2113_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (491628696997500 : Int) atom2113) := by
  rw [SparsePolynomial.eval_scale, eval_atom2113]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2113Coded : CoefficientMerge.Poly := [(nat_lit 5663, Int.ofNat (nat_lit 1))]
theorem atom2113Coded_decode : atom2113 = SparsePolynomial.decodeCubic 24 atom2113Coded := by decide +kernel
theorem atom2113Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (491628696997500 : Int) atom2113Coded) := by
  have h := atom2113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2114 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2114 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2114 = ((g 9) * (g 20) * (g 20)) := by
  norm_num [atom2114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2114_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315170406616032 : Int) atom2114) := by
  rw [SparsePolynomial.eval_scale, eval_atom2114]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2114Coded : CoefficientMerge.Poly := [(nat_lit 5684, Int.ofNat (nat_lit 1))]
theorem atom2114Coded_decode : atom2114 = SparsePolynomial.decodeCubic 24 atom2114Coded := by decide +kernel
theorem atom2114Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315170406616032 : Int) atom2114Coded) := by
  have h := atom2114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2115 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2115 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2115 = ((g 9) * (g 20) * (g 21)) := by
  norm_num [atom2115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2115_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (486539955846648 : Int) atom2115) := by
  rw [SparsePolynomial.eval_scale, eval_atom2115]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2115Coded : CoefficientMerge.Poly := [(nat_lit 5685, Int.ofNat (nat_lit 1))]
theorem atom2115Coded_decode : atom2115 = SparsePolynomial.decodeCubic 24 atom2115Coded := by decide +kernel
theorem atom2115Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (486539955846648 : Int) atom2115Coded) := by
  have h := atom2115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2116 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2116 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2116 = ((g 9) * (g 20) * (g 22)) := by
  norm_num [atom2116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2116_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399235093045728 : Int) atom2116) := by
  rw [SparsePolynomial.eval_scale, eval_atom2116]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2116Coded : CoefficientMerge.Poly := [(nat_lit 5686, Int.ofNat (nat_lit 1))]
theorem atom2116Coded_decode : atom2116 = SparsePolynomial.decodeCubic 24 atom2116Coded := by decide +kernel
theorem atom2116Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399235093045728 : Int) atom2116Coded) := by
  have h := atom2116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2117 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2117 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2117 = ((g 9) * (g 20) * (g 23)) := by
  norm_num [atom2117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2117_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482565818257596 : Int) atom2117) := by
  rw [SparsePolynomial.eval_scale, eval_atom2117]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2117Coded : CoefficientMerge.Poly := [(nat_lit 5687, Int.ofNat (nat_lit 1))]
theorem atom2117Coded_decode : atom2117 = SparsePolynomial.decodeCubic 24 atom2117Coded := by decide +kernel
theorem atom2117Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482565818257596 : Int) atom2117Coded) := by
  have h := atom2117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2118 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2118 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2118 = ((g 9) * (g 21) * (g 21)) := by
  norm_num [atom2118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2118_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110428842839832 : Int) atom2118) := by
  rw [SparsePolynomial.eval_scale, eval_atom2118]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 9) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2118Coded : CoefficientMerge.Poly := [(nat_lit 5709, Int.ofNat (nat_lit 1))]
theorem atom2118Coded_decode : atom2118 = SparsePolynomial.decodeCubic 24 atom2118Coded := by decide +kernel
theorem atom2118Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110428842839832 : Int) atom2118Coded) := by
  have h := atom2118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2119 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2119 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2119 = ((g 9) * (g 21) * (g 22)) := by
  norm_num [atom2119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2119_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180543118688352 : Int) atom2119) := by
  rw [SparsePolynomial.eval_scale, eval_atom2119]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 9) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2119Coded : CoefficientMerge.Poly := [(nat_lit 5710, Int.ofNat (nat_lit 1))]
theorem atom2119Coded_decode : atom2119 = SparsePolynomial.decodeCubic 24 atom2119Coded := by decide +kernel
theorem atom2119Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (180543118688352 : Int) atom2119Coded) := by
  have h := atom2119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2120 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2120 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2120 = ((g 9) * (g 21) * (g 23)) := by
  norm_num [atom2120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2120_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (252854208995580 : Int) atom2120) := by
  rw [SparsePolynomial.eval_scale, eval_atom2120]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 9) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2120Coded : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 1))]
theorem atom2120Coded_decode : atom2120 = SparsePolynomial.decodeCubic 24 atom2120Coded := by decide +kernel
theorem atom2120Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (252854208995580 : Int) atom2120Coded) := by
  have h := atom2120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2121 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom2121 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2121 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom2121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2121_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5779150700400 : Int) atom2121) := by
  rw [SparsePolynomial.eval_scale, eval_atom2121]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2121Coded : CoefficientMerge.Poly := [(nat_lit 6010, Int.ofNat (nat_lit 1))]
theorem atom2121Coded_decode : atom2121 = SparsePolynomial.decodeCubic 24 atom2121Coded := by decide +kernel
theorem atom2121Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5779150700400 : Int) atom2121Coded) := by
  have h := atom2121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2122 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom2122 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2122 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom2122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2122_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2122) := by
  rw [SparsePolynomial.eval_scale, eval_atom2122]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2122Coded : CoefficientMerge.Poly := [(nat_lit 6011, Int.ofNat (nat_lit 1))]
theorem atom2122Coded_decode : atom2122 = SparsePolynomial.decodeCubic 24 atom2122Coded := by decide +kernel
theorem atom2122Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2122Coded) := by
  have h := atom2122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2123 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom2123 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2123 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom2123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2123_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11430505825200 : Int) atom2123) := by
  rw [SparsePolynomial.eval_scale, eval_atom2123]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2123Coded : CoefficientMerge.Poly := [(nat_lit 6035, Int.ofNat (nat_lit 1))]
theorem atom2123Coded_decode : atom2123 = SparsePolynomial.decodeCubic 24 atom2123Coded := by decide +kernel
theorem atom2123Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11430505825200 : Int) atom2123Coded) := by
  have h := atom2123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2124 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2124 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2124 = ((g 10) * (g 11) * (g 16)) := by
  norm_num [atom2124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2124_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2124) := by
  rw [SparsePolynomial.eval_scale, eval_atom2124]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2124Coded : CoefficientMerge.Poly := [(nat_lit 6040, Int.ofNat (nat_lit 1))]
theorem atom2124Coded_decode : atom2124 = SparsePolynomial.decodeCubic 24 atom2124Coded := by decide +kernel
theorem atom2124Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2124Coded) := by
  have h := atom2124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2125 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2125 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2125 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom2125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2125_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2125) := by
  rw [SparsePolynomial.eval_scale, eval_atom2125]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2125Coded : CoefficientMerge.Poly := [(nat_lit 6041, Int.ofNat (nat_lit 1))]
theorem atom2125Coded_decode : atom2125 = SparsePolynomial.decodeCubic 24 atom2125Coded := by decide +kernel
theorem atom2125Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2125Coded) := by
  have h := atom2125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2126 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2126 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2126 = ((g 10) * (g 11) * (g 18)) := by
  norm_num [atom2126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2126_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7827040153152 : Int) atom2126) := by
  rw [SparsePolynomial.eval_scale, eval_atom2126]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2126Coded : CoefficientMerge.Poly := [(nat_lit 6042, Int.ofNat (nat_lit 1))]
theorem atom2126Coded_decode : atom2126 = SparsePolynomial.decodeCubic 24 atom2126Coded := by decide +kernel
theorem atom2126Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7827040153152 : Int) atom2126Coded) := by
  have h := atom2126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2127 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2127 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2127 = ((g 10) * (g 11) * (g 21)) := by
  norm_num [atom2127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2127_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48552573484800 : Int) atom2127) := by
  rw [SparsePolynomial.eval_scale, eval_atom2127]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 10) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2127Coded : CoefficientMerge.Poly := [(nat_lit 6045, Int.ofNat (nat_lit 1))]
theorem atom2127Coded_decode : atom2127 = SparsePolynomial.decodeCubic 24 atom2127Coded := by decide +kernel
theorem atom2127Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48552573484800 : Int) atom2127Coded) := by
  have h := atom2127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2128 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2128 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2128 = ((g 10) * (g 11) * (g 22)) := by
  norm_num [atom2128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2128_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93303439004160 : Int) atom2128) := by
  rw [SparsePolynomial.eval_scale, eval_atom2128]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 10) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2128Coded : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 1))]
theorem atom2128Coded_decode : atom2128 = SparsePolynomial.decodeCubic 24 atom2128Coded := by decide +kernel
theorem atom2128Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (93303439004160 : Int) atom2128Coded) := by
  have h := atom2128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block028 : CoefficientMerge.Poly := [(nat_lit 5487, Int.ofNat (nat_lit 38340001576800)), (nat_lit 5488, Int.ofNat (nat_lit 44527345077600)), (nat_lit 5489, Int.ofNat (nat_lit 50714688578400)), (nat_lit 5490, Int.ofNat (nat_lit 73791992737584)), (nat_lit 5491, Int.ofNat (nat_lit 44842698616320)), (nat_lit 5492, Int.ofNat (nat_lit 125939444689872)), (nat_lit 5493, Int.ofNat (nat_lit 151220555232120)), (nat_lit 5494, Int.ofNat (nat_lit 246175983184032)), (nat_lit 5495, Int.ofNat (nat_lit 354181063490100)), (nat_lit 5509, Int.ofNat (nat_lit 34312779824400)), (nat_lit 5510, Int.ofNat (nat_lit 62507318781600)), (nat_lit 5511, Int.ofNat (nat_lit 65632884055200)), (nat_lit 5512, Int.ofNat (nat_lit 71841489904800)), (nat_lit 5513, Int.ofNat (nat_lit 78050095754400)), (nat_lit 5514, Int.ofNat (nat_lit 101889785997648)), (nat_lit 5515, Int.ofNat (nat_lit 86927253684480)), (nat_lit 5516, Int.ofNat (nat_lit 183967270491312)), (nat_lit 5517, Int.ofNat (nat_lit 210863159270280)), (nat_lit 5518, Int.ofNat (nat_lit 315137321329248)), (nat_lit 5519, Int.ofNat (nat_lit 431271363530700)), (nat_lit 5534, Int.ofNat (nat_lit 53879456307600)), (nat_lit 5535, Int.ofNat (nat_lit 104750290260000)), (nat_lit 5536, Int.ofNat (nat_lit 109959565716000)), (nat_lit 5537, Int.ofNat (nat_lit 115168841172000)), (nat_lit 5538, Int.ofNat (nat_lit 126017705320848)), (nat_lit 5539, Int.ofNat (nat_lit 127362899458080)), (nat_lit 5540, Int.ofNat (nat_lit 231267918963312)), (nat_lit 5541, Int.ofNat (nat_lit 269059953741480)), (nat_lit 5542, Int.ofNat (nat_lit 363851473030848)), (nat_lit 5543, Int.ofNat (nat_lit 482737543249500)), (nat_lit 5559, Int.ofNat (nat_lit 79638791878800)), (nat_lit 5560, Int.ofNat (nat_lit 149114181031200)), (nat_lit 5561, Int.ofNat (nat_lit 152303533351200)), (nat_lit 5562, Int.ofNat (nat_lit 172326134536848)), (nat_lit 5563, Int.ofNat (nat_lit 173510210004480)), (nat_lit 5564, Int.ofNat (nat_lit 315536083923312)), (nat_lit 5565, Int.ofNat (nat_lit 367921016349480)), (nat_lit 5566, Int.ofNat (nat_lit 406502174209248)), (nat_lit 5567, Int.ofNat (nat_lit 524779126458300)), (nat_lit 5584, Int.ofNat (nat_lit 101326387654800)), (nat_lit 5585, Int.ofNat (nat_lit 199718571175200)), (nat_lit 5586, Int.ofNat (nat_lit 200900798383248)), (nat_lit 5587, Int.ofNat (nat_lit 215153486599680)), (nat_lit 5588, Int.ofNat (nat_lit 370247973267312)), (nat_lit 5589, Int.ofNat (nat_lit 434270175779880)), (nat_lit 5590, Int.ofNat (nat_lit 426695606746848)), (nat_lit 5591, Int.ofNat (nat_lit 632428948727100)), (nat_lit 5609, Int.ofNat (nat_lit 125452066093200)), (nat_lit 5610, Int.ofNat (nat_lit 244374569916048)), (nat_lit 5611, Int.ofNat (nat_lit 276662240110080)), (nat_lit 5612, Int.ofNat (nat_lit 449791708755312)), (nat_lit 5613, Int.ofNat (nat_lit 527934365968680)), (nat_lit 5614, Int.ofNat (nat_lit 533356568718048)), (nat_lit 5615, Int.ofNat (nat_lit 751253101760700)), (nat_lit 5634, Int.ofNat (nat_lit 164172690291456)), (nat_lit 5635, Int.ofNat (nat_lit 341402349779568)), (nat_lit 5636, Int.ofNat (nat_lit 565722016653024)), (nat_lit 5637, Int.ofNat (nat_lit 601102415080728)), (nat_lit 5638, Int.ofNat (nat_lit 501233644103904)), (nat_lit 5639, Int.ofNat (nat_lit 739294473362940)), (nat_lit 5659, Int.ofNat (nat_lit 112255485529968)), (nat_lit 5660, Int.ofNat (nat_lit 421979166878544)), (nat_lit 5661, Int.ofNat (nat_lit 455795061431688)), (nat_lit 5662, Int.ofNat (nat_lit 407529927423456)), (nat_lit 5663, Int.ofNat (nat_lit 491628696997500)), (nat_lit 5684, Int.ofNat (nat_lit 315170406616032)), (nat_lit 5685, Int.ofNat (nat_lit 486539955846648)), (nat_lit 5686, Int.ofNat (nat_lit 399235093045728)), (nat_lit 5687, Int.ofNat (nat_lit 482565818257596)), (nat_lit 5709, Int.ofNat (nat_lit 110428842839832)), (nat_lit 5710, Int.ofNat (nat_lit 180543118688352)), (nat_lit 5711, Int.ofNat (nat_lit 252854208995580)), (nat_lit 6010, Int.ofNat (nat_lit 5779150700400)), (nat_lit 6011, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6035, Int.ofNat (nat_lit 11430505825200)), (nat_lit 6040, Int.ofNat (nat_lit 3083040576000)), (nat_lit 6041, Int.ofNat (nat_lit 6166081152000)), (nat_lit 6042, Int.ofNat (nat_lit 7827040153152)), (nat_lit 6045, Int.ofNat (nat_lit 48552573484800)), (nat_lit 6046, Int.ofNat (nat_lit 93303439004160))]
theorem block028_data : block028 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38340001576800 : Int) atom2049Coded) (CoefficientMerge.scale (44527345077600 : Int) atom2050Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50714688578400 : Int) atom2051Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73791992737584 : Int) atom2052Coded) (CoefficientMerge.scale (44842698616320 : Int) atom2053Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125939444689872 : Int) atom2054Coded) (CoefficientMerge.scale (151220555232120 : Int) atom2055Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (246175983184032 : Int) atom2056Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354181063490100 : Int) atom2057Coded) (CoefficientMerge.scale (34312779824400 : Int) atom2058Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62507318781600 : Int) atom2059Coded) (CoefficientMerge.scale (65632884055200 : Int) atom2060Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71841489904800 : Int) atom2061Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78050095754400 : Int) atom2062Coded) (CoefficientMerge.scale (101889785997648 : Int) atom2063Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86927253684480 : Int) atom2064Coded) (CoefficientMerge.scale (183967270491312 : Int) atom2065Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210863159270280 : Int) atom2066Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315137321329248 : Int) atom2067Coded) (CoefficientMerge.scale (431271363530700 : Int) atom2068Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53879456307600 : Int) atom2069Coded) (CoefficientMerge.scale (104750290260000 : Int) atom2070Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109959565716000 : Int) atom2071Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115168841172000 : Int) atom2072Coded) (CoefficientMerge.scale (126017705320848 : Int) atom2073Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (127362899458080 : Int) atom2074Coded) (CoefficientMerge.scale (231267918963312 : Int) atom2075Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269059953741480 : Int) atom2076Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (363851473030848 : Int) atom2077Coded) (CoefficientMerge.scale (482737543249500 : Int) atom2078Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79638791878800 : Int) atom2079Coded) (CoefficientMerge.scale (149114181031200 : Int) atom2080Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152303533351200 : Int) atom2081Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172326134536848 : Int) atom2082Coded) (CoefficientMerge.scale (173510210004480 : Int) atom2083Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (315536083923312 : Int) atom2084Coded) (CoefficientMerge.scale (367921016349480 : Int) atom2085Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406502174209248 : Int) atom2086Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524779126458300 : Int) atom2087Coded) (CoefficientMerge.scale (101326387654800 : Int) atom2088Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199718571175200 : Int) atom2089Coded) (CoefficientMerge.scale (200900798383248 : Int) atom2090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215153486599680 : Int) atom2091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370247973267312 : Int) atom2092Coded) (CoefficientMerge.scale (434270175779880 : Int) atom2093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426695606746848 : Int) atom2094Coded) (CoefficientMerge.scale (632428948727100 : Int) atom2095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125452066093200 : Int) atom2096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (244374569916048 : Int) atom2097Coded) (CoefficientMerge.scale (276662240110080 : Int) atom2098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449791708755312 : Int) atom2099Coded) (CoefficientMerge.scale (527934365968680 : Int) atom2100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (533356568718048 : Int) atom2101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (751253101760700 : Int) atom2102Coded) (CoefficientMerge.scale (164172690291456 : Int) atom2103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (341402349779568 : Int) atom2104Coded) (CoefficientMerge.scale (565722016653024 : Int) atom2105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (601102415080728 : Int) atom2106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (501233644103904 : Int) atom2107Coded) (CoefficientMerge.scale (739294473362940 : Int) atom2108Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (112255485529968 : Int) atom2109Coded) (CoefficientMerge.scale (421979166878544 : Int) atom2110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (455795061431688 : Int) atom2111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407529927423456 : Int) atom2112Coded) (CoefficientMerge.scale (491628696997500 : Int) atom2113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (315170406616032 : Int) atom2114Coded) (CoefficientMerge.scale (486539955846648 : Int) atom2115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399235093045728 : Int) atom2116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482565818257596 : Int) atom2117Coded) (CoefficientMerge.scale (110428842839832 : Int) atom2118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180543118688352 : Int) atom2119Coded) (CoefficientMerge.scale (252854208995580 : Int) atom2120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5779150700400 : Int) atom2121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2122Coded) (CoefficientMerge.scale (11430505825200 : Int) atom2123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2124Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7827040153152 : Int) atom2126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48552573484800 : Int) atom2127Coded) (CoefficientMerge.scale (93303439004160 : Int) atom2128Coded)))))))) := by decide +kernel
theorem block028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block028 := by
  rw [block028_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2049Coded_nonneg g hg hA hB) (atom2050Coded_nonneg g hg hA hB)) (add_nonneg (atom2051Coded_nonneg g hg hA hB) (add_nonneg (atom2052Coded_nonneg g hg hA hB) (atom2053Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2054Coded_nonneg g hg hA hB) (atom2055Coded_nonneg g hg hA hB)) (add_nonneg (atom2056Coded_nonneg g hg hA hB) (add_nonneg (atom2057Coded_nonneg g hg hA hB) (atom2058Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2059Coded_nonneg g hg hA hB) (atom2060Coded_nonneg g hg hA hB)) (add_nonneg (atom2061Coded_nonneg g hg hA hB) (add_nonneg (atom2062Coded_nonneg g hg hA hB) (atom2063Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2064Coded_nonneg g hg hA hB) (atom2065Coded_nonneg g hg hA hB)) (add_nonneg (atom2066Coded_nonneg g hg hA hB) (add_nonneg (atom2067Coded_nonneg g hg hA hB) (atom2068Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2069Coded_nonneg g hg hA hB) (atom2070Coded_nonneg g hg hA hB)) (add_nonneg (atom2071Coded_nonneg g hg hA hB) (add_nonneg (atom2072Coded_nonneg g hg hA hB) (atom2073Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2074Coded_nonneg g hg hA hB) (atom2075Coded_nonneg g hg hA hB)) (add_nonneg (atom2076Coded_nonneg g hg hA hB) (add_nonneg (atom2077Coded_nonneg g hg hA hB) (atom2078Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2079Coded_nonneg g hg hA hB) (atom2080Coded_nonneg g hg hA hB)) (add_nonneg (atom2081Coded_nonneg g hg hA hB) (add_nonneg (atom2082Coded_nonneg g hg hA hB) (atom2083Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2084Coded_nonneg g hg hA hB) (atom2085Coded_nonneg g hg hA hB)) (add_nonneg (atom2086Coded_nonneg g hg hA hB) (add_nonneg (atom2087Coded_nonneg g hg hA hB) (atom2088Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2089Coded_nonneg g hg hA hB) (atom2090Coded_nonneg g hg hA hB)) (add_nonneg (atom2091Coded_nonneg g hg hA hB) (add_nonneg (atom2092Coded_nonneg g hg hA hB) (atom2093Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2094Coded_nonneg g hg hA hB) (atom2095Coded_nonneg g hg hA hB)) (add_nonneg (atom2096Coded_nonneg g hg hA hB) (add_nonneg (atom2097Coded_nonneg g hg hA hB) (atom2098Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2099Coded_nonneg g hg hA hB) (atom2100Coded_nonneg g hg hA hB)) (add_nonneg (atom2101Coded_nonneg g hg hA hB) (add_nonneg (atom2102Coded_nonneg g hg hA hB) (atom2103Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2104Coded_nonneg g hg hA hB) (atom2105Coded_nonneg g hg hA hB)) (add_nonneg (atom2106Coded_nonneg g hg hA hB) (add_nonneg (atom2107Coded_nonneg g hg hA hB) (atom2108Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2109Coded_nonneg g hg hA hB) (atom2110Coded_nonneg g hg hA hB)) (add_nonneg (atom2111Coded_nonneg g hg hA hB) (add_nonneg (atom2112Coded_nonneg g hg hA hB) (atom2113Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2114Coded_nonneg g hg hA hB) (atom2115Coded_nonneg g hg hA hB)) (add_nonneg (atom2116Coded_nonneg g hg hA hB) (add_nonneg (atom2117Coded_nonneg g hg hA hB) (atom2118Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2119Coded_nonneg g hg hA hB) (atom2120Coded_nonneg g hg hA hB)) (add_nonneg (atom2121Coded_nonneg g hg hA hB) (add_nonneg (atom2122Coded_nonneg g hg hA hB) (atom2123Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2124Coded_nonneg g hg hA hB) (atom2125Coded_nonneg g hg hA hB)) (add_nonneg (atom2126Coded_nonneg g hg hA hB) (add_nonneg (atom2127Coded_nonneg g hg hA hB) (atom2128Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
