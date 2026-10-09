import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0336 : SparsePolynomial.Poly := [([0,13,16], 1)]
theorem eval_atom0336 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 0) * (g 13) * (g 16)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30929874548400 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336Coded : CoefficientMerge.Poly := [(289, 1)]
theorem atom0336Coded_decode : atom0336 = SparsePolynomial.decodeCubic 21 atom0336Coded := by decide +kernel
theorem atom0336Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30929874548400 : Int) atom0336Coded) := by
  have h := atom0336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0337 : SparsePolynomial.Poly := [([0,13,17], 1)]
theorem eval_atom0337 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 0) * (g 13) * (g 17)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27676226793600 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337Coded : CoefficientMerge.Poly := [(290, 1)]
theorem atom0337Coded_decode : atom0337 = SparsePolynomial.decodeCubic 21 atom0337Coded := by decide +kernel
theorem atom0337Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27676226793600 : Int) atom0337Coded) := by
  have h := atom0337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0338 : SparsePolynomial.Poly := [([0,13,18], 1)]
theorem eval_atom0338 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 0) * (g 13) * (g 18)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19355019465600 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338Coded : CoefficientMerge.Poly := [(291, 1)]
theorem atom0338Coded_decode : atom0338 = SparsePolynomial.decodeCubic 21 atom0338Coded := by decide +kernel
theorem atom0338Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19355019465600 : Int) atom0338Coded) := by
  have h := atom0338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0339 : SparsePolynomial.Poly := [([0,13,19], 1)]
theorem eval_atom0339 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 0) * (g 13) * (g 19)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14192212251600 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339Coded : CoefficientMerge.Poly := [(292, 1)]
theorem atom0339Coded_decode : atom0339 = SparsePolynomial.decodeCubic 21 atom0339Coded := by decide +kernel
theorem atom0339Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14192212251600 : Int) atom0339Coded) := by
  have h := atom0339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0340 : SparsePolynomial.Poly := [([0,13,20], 1)]
theorem eval_atom0340 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 0) * (g 13) * (g 20)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10448028259200 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340Coded : CoefficientMerge.Poly := [(293, 1)]
theorem atom0340Coded_decode : atom0340 = SparsePolynomial.decodeCubic 21 atom0340Coded := by decide +kernel
theorem atom0340Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10448028259200 : Int) atom0340Coded) := by
  have h := atom0340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0341 : SparsePolynomial.Poly := [([0,14,14], 1)]
theorem eval_atom0341 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 0) * (g 14) * (g 14)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22957537881600 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341Coded : CoefficientMerge.Poly := [(308, 1)]
theorem atom0341Coded_decode : atom0341 = SparsePolynomial.decodeCubic 21 atom0341Coded := by decide +kernel
theorem atom0341Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22957537881600 : Int) atom0341Coded) := by
  have h := atom0341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0342 : SparsePolynomial.Poly := [([0,14,15], 1)]
theorem eval_atom0342 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 0) * (g 14) * (g 15)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40599005328000 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342Coded : CoefficientMerge.Poly := [(309, 1)]
theorem atom0342Coded_decode : atom0342 = SparsePolynomial.decodeCubic 21 atom0342Coded := by decide +kernel
theorem atom0342Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40599005328000 : Int) atom0342Coded) := by
  have h := atom0342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0343 : SparsePolynomial.Poly := [([0,14,16], 1)]
theorem eval_atom0343 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 0) * (g 14) * (g 16)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32015781705600 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343Coded : CoefficientMerge.Poly := [(310, 1)]
theorem atom0343Coded_decode : atom0343 = SparsePolynomial.decodeCubic 21 atom0343Coded := by decide +kernel
theorem atom0343Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32015781705600 : Int) atom0343Coded) := by
  have h := atom0343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0344 : SparsePolynomial.Poly := [([0,14,17], 1)]
theorem eval_atom0344 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 0) * (g 14) * (g 17)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29965795171200 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344Coded : CoefficientMerge.Poly := [(311, 1)]
theorem atom0344Coded_decode : atom0344 = SparsePolynomial.decodeCubic 21 atom0344Coded := by decide +kernel
theorem atom0344Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29965795171200 : Int) atom0344Coded) := by
  have h := atom0344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0345 : SparsePolynomial.Poly := [([0,14,18], 1)]
theorem eval_atom0345 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 0) * (g 14) * (g 18)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21942260726400 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345Coded : CoefficientMerge.Poly := [(312, 1)]
theorem atom0345Coded_decode : atom0345 = SparsePolynomial.decodeCubic 21 atom0345Coded := by decide +kernel
theorem atom0345Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21942260726400 : Int) atom0345Coded) := by
  have h := atom0345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0346 : SparsePolynomial.Poly := [([0,14,19], 1)]
theorem eval_atom0346 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 0) * (g 14) * (g 19)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14664738614400 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346Coded : CoefficientMerge.Poly := [(313, 1)]
theorem atom0346Coded_decode : atom0346 = SparsePolynomial.decodeCubic 21 atom0346Coded := by decide +kernel
theorem atom0346Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14664738614400 : Int) atom0346Coded) := by
  have h := atom0346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0347 : SparsePolynomial.Poly := [([0,14,20], 1)]
theorem eval_atom0347 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 0) * (g 14) * (g 20)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12517241385600 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347Coded : CoefficientMerge.Poly := [(314, 1)]
theorem atom0347Coded_decode : atom0347 = SparsePolynomial.decodeCubic 21 atom0347Coded := by decide +kernel
theorem atom0347Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12517241385600 : Int) atom0347Coded) := by
  have h := atom0347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0348 : SparsePolynomial.Poly := [([0,15,15], 1)]
theorem eval_atom0348 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 0) * (g 15) * (g 15)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23040654336000 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348Coded : CoefficientMerge.Poly := [(330, 1)]
theorem atom0348Coded_decode : atom0348 = SparsePolynomial.decodeCubic 21 atom0348Coded := by decide +kernel
theorem atom0348Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23040654336000 : Int) atom0348Coded) := by
  have h := atom0348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0349 : SparsePolynomial.Poly := [([0,15,16], 1)]
theorem eval_atom0349 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 0) * (g 15) * (g 16)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39225167654400 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349Coded : CoefficientMerge.Poly := [(331, 1)]
theorem atom0349Coded_decode : atom0349 = SparsePolynomial.decodeCubic 21 atom0349Coded := by decide +kernel
theorem atom0349Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39225167654400 : Int) atom0349Coded) := by
  have h := atom0349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0350 : SparsePolynomial.Poly := [([0,15,17], 1)]
theorem eval_atom0350 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 0) * (g 15) * (g 17)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40376131084800 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350Coded : CoefficientMerge.Poly := [(332, 1)]
theorem atom0350Coded_decode : atom0350 = SparsePolynomial.decodeCubic 21 atom0350Coded := by decide +kernel
theorem atom0350Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40376131084800 : Int) atom0350Coded) := by
  have h := atom0350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0351 : SparsePolynomial.Poly := [([0,15,18], 1)]
theorem eval_atom0351 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 0) * (g 15) * (g 18)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34037154547200 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351Coded : CoefficientMerge.Poly := [(333, 1)]
theorem atom0351Coded_decode : atom0351 = SparsePolynomial.decodeCubic 21 atom0351Coded := by decide +kernel
theorem atom0351Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34037154547200 : Int) atom0351Coded) := by
  have h := atom0351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0352 : SparsePolynomial.Poly := [([0,15,19], 1)]
theorem eval_atom0352 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 0) * (g 15) * (g 19)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19513520611200 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352Coded : CoefficientMerge.Poly := [(334, 1)]
theorem atom0352Coded_decode : atom0352 = SparsePolynomial.decodeCubic 21 atom0352Coded := by decide +kernel
theorem atom0352Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19513520611200 : Int) atom0352Coded) := by
  have h := atom0352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0353 : SparsePolynomial.Poly := [([0,15,20], 1)]
theorem eval_atom0353 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 0) * (g 15) * (g 20)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20827437120000 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353Coded : CoefficientMerge.Poly := [(335, 1)]
theorem atom0353Coded_decode : atom0353 = SparsePolynomial.decodeCubic 21 atom0353Coded := by decide +kernel
theorem atom0353Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20827437120000 : Int) atom0353Coded) := by
  have h := atom0353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0354 : SparsePolynomial.Poly := [([0,16,16], 1)]
theorem eval_atom0354 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 0) * (g 16) * (g 16)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16982044692480 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354Coded : CoefficientMerge.Poly := [(352, 1)]
theorem atom0354Coded_decode : atom0354 = SparsePolynomial.decodeCubic 21 atom0354Coded := by decide +kernel
theorem atom0354Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16982044692480 : Int) atom0354Coded) := by
  have h := atom0354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0355 : SparsePolynomial.Poly := [([0,16,17], 1)]
theorem eval_atom0355 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 0) * (g 16) * (g 17)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33350960563200 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355Coded : CoefficientMerge.Poly := [(353, 1)]
theorem atom0355Coded_decode : atom0355 = SparsePolynomial.decodeCubic 21 atom0355Coded := by decide +kernel
theorem atom0355Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33350960563200 : Int) atom0355Coded) := by
  have h := atom0355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0356 : SparsePolynomial.Poly := [([0,16,18], 1)]
theorem eval_atom0356 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 0) * (g 16) * (g 18)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35187254323200 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356Coded : CoefficientMerge.Poly := [(354, 1)]
theorem atom0356Coded_decode : atom0356 = SparsePolynomial.decodeCubic 21 atom0356Coded := by decide +kernel
theorem atom0356Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35187254323200 : Int) atom0356Coded) := by
  have h := atom0356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0357 : SparsePolynomial.Poly := [([0,16,19], 1)]
theorem eval_atom0357 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 0) * (g 16) * (g 19)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20310858691200 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357Coded : CoefficientMerge.Poly := [(355, 1)]
theorem atom0357Coded_decode : atom0357 = SparsePolynomial.decodeCubic 21 atom0357Coded := by decide +kernel
theorem atom0357Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20310858691200 : Int) atom0357Coded) := by
  have h := atom0357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0358 : SparsePolynomial.Poly := [([0,16,20], 1)]
theorem eval_atom0358 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 0) * (g 16) * (g 20)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22313868595200 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358Coded : CoefficientMerge.Poly := [(356, 1)]
theorem atom0358Coded_decode : atom0358 = SparsePolynomial.decodeCubic 21 atom0358Coded := by decide +kernel
theorem atom0358Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22313868595200 : Int) atom0358Coded) := by
  have h := atom0358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0359 : SparsePolynomial.Poly := [([0,17,17], 1)]
theorem eval_atom0359 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 0) * (g 17) * (g 17)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17166447244800 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359Coded : CoefficientMerge.Poly := [(374, 1)]
theorem atom0359Coded_decode : atom0359 = SparsePolynomial.decodeCubic 21 atom0359Coded := by decide +kernel
theorem atom0359Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17166447244800 : Int) atom0359Coded) := by
  have h := atom0359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0360 : SparsePolynomial.Poly := [([0,17,18], 1)]
theorem eval_atom0360 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 0) * (g 17) * (g 18)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36337354099200 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360Coded : CoefficientMerge.Poly := [(375, 1)]
theorem atom0360Coded_decode : atom0360 = SparsePolynomial.decodeCubic 21 atom0360Coded := by decide +kernel
theorem atom0360Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36337354099200 : Int) atom0360Coded) := by
  have h := atom0360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0361 : SparsePolynomial.Poly := [([0,17,19], 1)]
theorem eval_atom0361 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 0) * (g 17) * (g 19)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20587269225600 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361Coded : CoefficientMerge.Poly := [(376, 1)]
theorem atom0361Coded_decode : atom0361 = SparsePolynomial.decodeCubic 21 atom0361Coded := by decide +kernel
theorem atom0361Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20587269225600 : Int) atom0361Coded) := by
  have h := atom0361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0362 : SparsePolynomial.Poly := [([0,17,20], 1)]
theorem eval_atom0362 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 0) * (g 17) * (g 20)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20398324262400 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362Coded : CoefficientMerge.Poly := [(377, 1)]
theorem atom0362Coded_decode : atom0362 = SparsePolynomial.decodeCubic 21 atom0362Coded := by decide +kernel
theorem atom0362Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20398324262400 : Int) atom0362Coded) := by
  have h := atom0362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0363 : SparsePolynomial.Poly := [([0,18,18], 1)]
theorem eval_atom0363 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 0) * (g 18) * (g 18)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18743726937600 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363Coded : CoefficientMerge.Poly := [(396, 1)]
theorem atom0363Coded_decode : atom0363 = SparsePolynomial.decodeCubic 21 atom0363Coded := by decide +kernel
theorem atom0363Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18743726937600 : Int) atom0363Coded) := by
  have h := atom0363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0364 : SparsePolynomial.Poly := [([0,18,19], 1)]
theorem eval_atom0364 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 0) * (g 18) * (g 19)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21384607305600 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364Coded : CoefficientMerge.Poly := [(397, 1)]
theorem atom0364Coded_decode : atom0364 = SparsePolynomial.decodeCubic 21 atom0364Coded := by decide +kernel
theorem atom0364Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21384607305600 : Int) atom0364Coded) := by
  have h := atom0364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0365 : SparsePolynomial.Poly := [([0,18,20], 1)]
theorem eval_atom0365 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 0) * (g 18) * (g 20)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21884755737600 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365Coded : CoefficientMerge.Poly := [(398, 1)]
theorem atom0365Coded_decode : atom0365 = SparsePolynomial.decodeCubic 21 atom0365Coded := by decide +kernel
theorem atom0365Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21884755737600 : Int) atom0365Coded) := by
  have h := atom0365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0366 : SparsePolynomial.Poly := [([0,19,19], 1)]
theorem eval_atom0366 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 0) * (g 19) * (g 19)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1655080560000 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366Coded : CoefficientMerge.Poly := [(418, 1)]
theorem atom0366Coded_decode : atom0366 = SparsePolynomial.decodeCubic 21 atom0366Coded := by decide +kernel
theorem atom0366Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1655080560000 : Int) atom0366Coded) := by
  have h := atom0366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0367 : SparsePolynomial.Poly := [([0,19,20], 1)]
theorem eval_atom0367 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 0) * (g 19) * (g 20)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2509440393600 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367Coded : CoefficientMerge.Poly := [(419, 1)]
theorem atom0367Coded_decode : atom0367 = SparsePolynomial.decodeCubic 21 atom0367Coded := by decide +kernel
theorem atom0367Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2509440393600 : Int) atom0367Coded) := by
  have h := atom0367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0368 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0368 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4803357888000 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368Coded : CoefficientMerge.Poly := [(464, 1)]
theorem atom0368Coded_decode : atom0368 = SparsePolynomial.decodeCubic 21 atom0368Coded := by decide +kernel
theorem atom0368Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4803357888000 : Int) atom0368Coded) := by
  have h := atom0368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0369 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0369 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4117163904000 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369Coded : CoefficientMerge.Poly := [(465, 1)]
theorem atom0369Coded_decode : atom0369 = SparsePolynomial.decodeCubic 21 atom0369Coded := by decide +kernel
theorem atom0369Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4117163904000 : Int) atom0369Coded) := by
  have h := atom0369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0370 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0370 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3430969920000 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370Coded : CoefficientMerge.Poly := [(466, 1)]
theorem atom0370Coded_decode : atom0370 = SparsePolynomial.decodeCubic 21 atom0370Coded := by decide +kernel
theorem atom0370Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3430969920000 : Int) atom0370Coded) := by
  have h := atom0370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0371 : SparsePolynomial.Poly := [([1,1,5], 1)]
theorem eval_atom0371 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4236153898752 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371Coded : CoefficientMerge.Poly := [(467, 1)]
theorem atom0371Coded_decode : atom0371 = SparsePolynomial.decodeCubic 21 atom0371Coded := by decide +kernel
theorem atom0371Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4236153898752 : Int) atom0371Coded) := by
  have h := atom0371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0372 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0372 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4003284902400 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372Coded : CoefficientMerge.Poly := [(468, 1)]
theorem atom0372Coded_decode : atom0372 = SparsePolynomial.decodeCubic 21 atom0372Coded := by decide +kernel
theorem atom0372Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4003284902400 : Int) atom0372Coded) := by
  have h := atom0372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0373 : SparsePolynomial.Poly := [([1,1,7], 1)]
theorem eval_atom0373 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 1) * (g 1) * (g 7)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4770887243904 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373Coded : CoefficientMerge.Poly := [(469, 1)]
theorem atom0373Coded_decode : atom0373 = SparsePolynomial.decodeCubic 21 atom0373Coded := by decide +kernel
theorem atom0373Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4770887243904 : Int) atom0373Coded) := by
  have h := atom0373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0374 : SparsePolynomial.Poly := [([1,1,8], 1)]
theorem eval_atom0374 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 1) * (g 1) * (g 8)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4586868518400 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374Coded : CoefficientMerge.Poly := [(470, 1)]
theorem atom0374Coded_decode : atom0374 = SparsePolynomial.decodeCubic 21 atom0374Coded := by decide +kernel
theorem atom0374Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4586868518400 : Int) atom0374Coded) := by
  have h := atom0374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0375 : SparsePolynomial.Poly := [([1,1,9], 1)]
theorem eval_atom0375 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4327854451200 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375Coded : CoefficientMerge.Poly := [(471, 1)]
theorem atom0375Coded_decode : atom0375 = SparsePolynomial.decodeCubic 21 atom0375Coded := by decide +kernel
theorem atom0375Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4327854451200 : Int) atom0375Coded) := by
  have h := atom0375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0376 : SparsePolynomial.Poly := [([1,1,10], 1)]
theorem eval_atom0376 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 1) * (g 1) * (g 10)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4068840384000 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376Coded : CoefficientMerge.Poly := [(472, 1)]
theorem atom0376Coded_decode : atom0376 = SparsePolynomial.decodeCubic 21 atom0376Coded := by decide +kernel
theorem atom0376Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4068840384000 : Int) atom0376Coded) := by
  have h := atom0376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0377 : SparsePolynomial.Poly := [([1,1,11], 1)]
theorem eval_atom0377 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 1) * (g 1) * (g 11)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3497902732800 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377Coded : CoefficientMerge.Poly := [(473, 1)]
theorem atom0377Coded_decode : atom0377 = SparsePolynomial.decodeCubic 21 atom0377Coded := by decide +kernel
theorem atom0377Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3497902732800 : Int) atom0377Coded) := by
  have h := atom0377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0378 : SparsePolynomial.Poly := [([1,1,12], 1)]
theorem eval_atom0378 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 1) * (g 1) * (g 12)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (877411942400 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378Coded : CoefficientMerge.Poly := [(474, 1)]
theorem atom0378Coded_decode : atom0378 = SparsePolynomial.decodeCubic 21 atom0378Coded := by decide +kernel
theorem atom0378Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (877411942400 : Int) atom0378Coded) := by
  have h := atom0378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0379 : SparsePolynomial.Poly := [([1,1,15], 1)]
theorem eval_atom0379 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 1) * (g 1) * (g 15)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4103633318400 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379Coded : CoefficientMerge.Poly := [(477, 1)]
theorem atom0379Coded_decode : atom0379 = SparsePolynomial.decodeCubic 21 atom0379Coded := by decide +kernel
theorem atom0379Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4103633318400 : Int) atom0379Coded) := by
  have h := atom0379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0380 : SparsePolynomial.Poly := [([1,1,17], 1)]
theorem eval_atom0380 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 1) * (g 1) * (g 17)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393250636800 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380Coded : CoefficientMerge.Poly := [(479, 1)]
theorem atom0380Coded_decode : atom0380 = SparsePolynomial.decodeCubic 21 atom0380Coded := by decide +kernel
theorem atom0380Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (393250636800 : Int) atom0380Coded) := by
  have h := atom0380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0381 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0381 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9359299353600 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381Coded : CoefficientMerge.Poly := [(485, 1)]
theorem atom0381Coded_decode : atom0381 = SparsePolynomial.decodeCubic 21 atom0381Coded := by decide +kernel
theorem atom0381Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9359299353600 : Int) atom0381Coded) := by
  have h := atom0381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0382 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0382 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17682542438400 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382Coded : CoefficientMerge.Poly := [(486, 1)]
theorem atom0382Coded_decode : atom0382 = SparsePolynomial.decodeCubic 21 atom0382Coded := by decide +kernel
theorem atom0382Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17682542438400 : Int) atom0382Coded) := by
  have h := atom0382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0383 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0383 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16646486169600 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383Coded : CoefficientMerge.Poly := [(487, 1)]
theorem atom0383Coded_decode : atom0383 = SparsePolynomial.decodeCubic 21 atom0383Coded := by decide +kernel
theorem atom0383Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16646486169600 : Int) atom0383Coded) := by
  have h := atom0383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0384 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0384 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18593185826304 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384Coded : CoefficientMerge.Poly := [(488, 1)]
theorem atom0384Coded_decode : atom0384 = SparsePolynomial.decodeCubic 21 atom0384Coded := by decide +kernel
theorem atom0384Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18593185826304 : Int) atom0384Coded) := by
  have h := atom0384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0385 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0385 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18463779532800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385Coded : CoefficientMerge.Poly := [(489, 1)]
theorem atom0385Coded_decode : atom0385 = SparsePolynomial.decodeCubic 21 atom0385Coded := by decide +kernel
theorem atom0385Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18463779532800 : Int) atom0385Coded) := by
  have h := atom0385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0386 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0386 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20335315915008 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386Coded : CoefficientMerge.Poly := [(490, 1)]
theorem atom0386Coded_decode : atom0386 = SparsePolynomial.decodeCubic 21 atom0386Coded := by decide +kernel
theorem atom0386Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20335315915008 : Int) atom0386Coded) := by
  have h := atom0386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0387 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0387 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20303610163200 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387Coded : CoefficientMerge.Poly := [(491, 1)]
theorem atom0387Coded_decode : atom0387 = SparsePolynomial.decodeCubic 21 atom0387Coded := by decide +kernel
theorem atom0387Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20303610163200 : Int) atom0387Coded) := by
  have h := atom0387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0388 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0388 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20121913728000 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388Coded : CoefficientMerge.Poly := [(492, 1)]
theorem atom0388Coded_decode : atom0388 = SparsePolynomial.decodeCubic 21 atom0388Coded := by decide +kernel
theorem atom0388Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20121913728000 : Int) atom0388Coded) := by
  have h := atom0388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0389 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0389 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19940217292800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389Coded : CoefficientMerge.Poly := [(493, 1)]
theorem atom0389Coded_decode : atom0389 = SparsePolynomial.decodeCubic 21 atom0389Coded := by decide +kernel
theorem atom0389Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19940217292800 : Int) atom0389Coded) := by
  have h := atom0389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0390 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0390 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19134673689600 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390Coded : CoefficientMerge.Poly := [(494, 1)]
theorem atom0390Coded_decode : atom0390 = SparsePolynomial.decodeCubic 21 atom0390Coded := by decide +kernel
theorem atom0390Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19134673689600 : Int) atom0390Coded) := by
  have h := atom0390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0391 : SparsePolynomial.Poly := [([1,2,12], 1)]
theorem eval_atom0391 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14230023808000 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391Coded : CoefficientMerge.Poly := [(495, 1)]
theorem atom0391Coded_decode : atom0391 = SparsePolynomial.decodeCubic 21 atom0391Coded := by decide +kernel
theorem atom0391Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14230023808000 : Int) atom0391Coded) := by
  have h := atom0391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0392 : SparsePolynomial.Poly := [([1,2,13], 1)]
theorem eval_atom0392 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12811531622400 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392Coded : CoefficientMerge.Poly := [(496, 1)]
theorem atom0392Coded_decode : atom0392 = SparsePolynomial.decodeCubic 21 atom0392Coded := by decide +kernel
theorem atom0392Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12811531622400 : Int) atom0392Coded) := by
  have h := atom0392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0393 : SparsePolynomial.Poly := [([1,2,14], 1)]
theorem eval_atom0393 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13147863321600 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393Coded : CoefficientMerge.Poly := [(497, 1)]
theorem atom0393Coded_decode : atom0393 = SparsePolynomial.decodeCubic 21 atom0393Coded := by decide +kernel
theorem atom0393Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13147863321600 : Int) atom0393Coded) := by
  have h := atom0393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0394 : SparsePolynomial.Poly := [([1,2,15], 1)]
theorem eval_atom0394 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 1) * (g 2) * (g 15)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22298405068800 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394Coded : CoefficientMerge.Poly := [(498, 1)]
theorem atom0394Coded_decode : atom0394 = SparsePolynomial.decodeCubic 21 atom0394Coded := by decide +kernel
theorem atom0394Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22298405068800 : Int) atom0394Coded) := by
  have h := atom0394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0395 : SparsePolynomial.Poly := [([1,2,16], 1)]
theorem eval_atom0395 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 1) * (g 2) * (g 16)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11832174950400 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395Coded : CoefficientMerge.Poly := [(499, 1)]
theorem atom0395Coded_decode : atom0395 = SparsePolynomial.decodeCubic 21 atom0395Coded := by decide +kernel
theorem atom0395Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11832174950400 : Int) atom0395Coded) := by
  have h := atom0395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0396 : SparsePolynomial.Poly := [([1,2,17], 1)]
theorem eval_atom0396 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 1) * (g 2) * (g 17)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18674799091200 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396Coded : CoefficientMerge.Poly := [(500, 1)]
theorem atom0396Coded_decode : atom0396 = SparsePolynomial.decodeCubic 21 atom0396Coded := by decide +kernel
theorem atom0396Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18674799091200 : Int) atom0396Coded) := by
  have h := atom0396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0397 : SparsePolynomial.Poly := [([1,2,18], 1)]
theorem eval_atom0397 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 1) * (g 2) * (g 18)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11176263705600 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397Coded : CoefficientMerge.Poly := [(501, 1)]
theorem atom0397Coded_decode : atom0397 = SparsePolynomial.decodeCubic 21 atom0397Coded := by decide +kernel
theorem atom0397Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11176263705600 : Int) atom0397Coded) := by
  have h := atom0397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0398 : SparsePolynomial.Poly := [([1,2,19], 1)]
theorem eval_atom0398 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 1) * (g 2) * (g 19)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7996898246400 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398Coded : CoefficientMerge.Poly := [(502, 1)]
theorem atom0398Coded_decode : atom0398 = SparsePolynomial.decodeCubic 21 atom0398Coded := by decide +kernel
theorem atom0398Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7996898246400 : Int) atom0398Coded) := by
  have h := atom0398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0399 : SparsePolynomial.Poly := [([1,2,20], 1)]
theorem eval_atom0399 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 1) * (g 2) * (g 20)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7905405715200 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399Coded : CoefficientMerge.Poly := [(503, 1)]
theorem atom0399Coded_decode : atom0399 = SparsePolynomial.decodeCubic 21 atom0399Coded := by decide +kernel
theorem atom0399Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7905405715200 : Int) atom0399Coded) := by
  have h := atom0399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0400 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0400 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7468883251200 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400Coded : CoefficientMerge.Poly := [(507, 1)]
theorem atom0400Coded_decode : atom0400 = SparsePolynomial.decodeCubic 21 atom0400Coded := by decide +kernel
theorem atom0400Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7468883251200 : Int) atom0400Coded) := by
  have h := atom0400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0401 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0401 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14238041932800 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401Coded : CoefficientMerge.Poly := [(508, 1)]
theorem atom0401Coded_decode : atom0401 = SparsePolynomial.decodeCubic 21 atom0401Coded := by decide +kernel
theorem atom0401Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14238041932800 : Int) atom0401Coded) := by
  have h := atom0401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0402 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0402 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16521073288704 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402Coded : CoefficientMerge.Poly := [(509, 1)]
theorem atom0402Coded_decode : atom0402 = SparsePolynomial.decodeCubic 21 atom0402Coded := by decide +kernel
theorem atom0402Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16521073288704 : Int) atom0402Coded) := by
  have h := atom0402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0403 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0403 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16727998694400 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403Coded : CoefficientMerge.Poly := [(510, 1)]
theorem atom0403Coded_decode : atom0403 = SparsePolynomial.decodeCubic 21 atom0403Coded := by decide +kernel
theorem atom0403Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16727998694400 : Int) atom0403Coded) := by
  have h := atom0403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0404 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0404 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18935866775808 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404Coded : CoefficientMerge.Poly := [(511, 1)]
theorem atom0404Coded_decode : atom0404 = SparsePolynomial.decodeCubic 21 atom0404Coded := by decide +kernel
theorem atom0404Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18935866775808 : Int) atom0404Coded) := by
  have h := atom0404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0405 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0405 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19240492723200 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405Coded : CoefficientMerge.Poly := [(512, 1)]
theorem atom0405Coded_decode : atom0405 = SparsePolynomial.decodeCubic 21 atom0405Coded := by decide +kernel
theorem atom0405Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19240492723200 : Int) atom0405Coded) := by
  have h := atom0405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0406 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0406 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19395127987200 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406Coded : CoefficientMerge.Poly := [(513, 1)]
theorem atom0406Coded_decode : atom0406 = SparsePolynomial.decodeCubic 21 atom0406Coded := by decide +kernel
theorem atom0406Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19395127987200 : Int) atom0406Coded) := by
  have h := atom0406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0407 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0407 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19549763251200 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407Coded : CoefficientMerge.Poly := [(514, 1)]
theorem atom0407Coded_decode : atom0407 = SparsePolynomial.decodeCubic 21 atom0407Coded := by decide +kernel
theorem atom0407Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19549763251200 : Int) atom0407Coded) := by
  have h := atom0407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0408 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0408 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19080551347200 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408Coded : CoefficientMerge.Poly := [(515, 1)]
theorem atom0408Coded_decode : atom0408 = SparsePolynomial.decodeCubic 21 atom0408Coded := by decide +kernel
theorem atom0408Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19080551347200 : Int) atom0408Coded) := by
  have h := atom0408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0409 : SparsePolynomial.Poly := [([1,3,12], 1)]
theorem eval_atom0409 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14512233164800 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409Coded : CoefficientMerge.Poly := [(516, 1)]
theorem atom0409Coded_decode : atom0409 = SparsePolynomial.decodeCubic 21 atom0409Coded := by decide +kernel
theorem atom0409Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14512233164800 : Int) atom0409Coded) := by
  have h := atom0409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0410 : SparsePolynomial.Poly := [([1,3,13], 1)]
theorem eval_atom0410 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13430072678400 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410Coded : CoefficientMerge.Poly := [(517, 1)]
theorem atom0410Coded_decode : atom0410 = SparsePolynomial.decodeCubic 21 atom0410Coded := by decide +kernel
theorem atom0410Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13430072678400 : Int) atom0410Coded) := by
  have h := atom0410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0411 : SparsePolynomial.Poly := [([1,3,14], 1)]
theorem eval_atom0411 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14102736076800 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411Coded : CoefficientMerge.Poly := [(518, 1)]
theorem atom0411Coded_decode : atom0411 = SparsePolynomial.decodeCubic 21 atom0411Coded := by decide +kernel
theorem atom0411Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14102736076800 : Int) atom0411Coded) := by
  have h := atom0411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0412 : SparsePolynomial.Poly := [([1,3,15], 1)]
theorem eval_atom0412 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 1) * (g 3) * (g 15)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23589609523200 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412Coded : CoefficientMerge.Poly := [(519, 1)]
theorem atom0412Coded_decode : atom0412 = SparsePolynomial.decodeCubic 21 atom0412Coded := by decide +kernel
theorem atom0412Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23589609523200 : Int) atom0412Coded) := by
  have h := atom0412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0413 : SparsePolynomial.Poly := [([1,3,16], 1)]
theorem eval_atom0413 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 1) * (g 3) * (g 16)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14801172019200 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413Coded : CoefficientMerge.Poly := [(520, 1)]
theorem atom0413Coded_decode : atom0413 = SparsePolynomial.decodeCubic 21 atom0413Coded := by decide +kernel
theorem atom0413Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14801172019200 : Int) atom0413Coded) := by
  have h := atom0413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0414 : SparsePolynomial.Poly := [([1,3,17], 1)]
theorem eval_atom0414 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 1) * (g 3) * (g 17)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20638666944000 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414Coded : CoefficientMerge.Poly := [(521, 1)]
theorem atom0414Coded_decode : atom0414 = SparsePolynomial.decodeCubic 21 atom0414Coded := by decide +kernel
theorem atom0414Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20638666944000 : Int) atom0414Coded) := by
  have h := atom0414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0415 : SparsePolynomial.Poly := [([1,3,18], 1)]
theorem eval_atom0415 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0415 = ((g 1) * (g 3) * (g 18)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0415_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15517648742400 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415Coded : CoefficientMerge.Poly := [(522, 1)]
theorem atom0415Coded_decode : atom0415 = SparsePolynomial.decodeCubic 21 atom0415Coded := by decide +kernel
theorem atom0415Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15517648742400 : Int) atom0415Coded) := by
  have h := atom0415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block006 : CoefficientMerge.Poly := [(289, 30929874548400), (290, 27676226793600), (291, 19355019465600), (292, 14192212251600), (293, 10448028259200), (308, 22957537881600), (309, 40599005328000), (310, 32015781705600), (311, 29965795171200), (312, 21942260726400), (313, 14664738614400), (314, 12517241385600), (330, 23040654336000), (331, 39225167654400), (332, 40376131084800), (333, 34037154547200), (334, 19513520611200), (335, 20827437120000), (352, 16982044692480), (353, 33350960563200), (354, 35187254323200), (355, 20310858691200), (356, 22313868595200), (374, 17166447244800), (375, 36337354099200), (376, 20587269225600), (377, 20398324262400), (396, 18743726937600), (397, 21384607305600), (398, 21884755737600), (418, 1655080560000), (419, 2509440393600), (464, 4803357888000), (465, 4117163904000), (466, 3430969920000), (467, 4236153898752), (468, 4003284902400), (469, 4770887243904), (470, 4586868518400), (471, 4327854451200), (472, 4068840384000), (473, 3497902732800), (474, 877411942400), (477, 4103633318400), (479, 393250636800), (485, 9359299353600), (486, 17682542438400), (487, 16646486169600), (488, 18593185826304), (489, 18463779532800), (490, 20335315915008), (491, 20303610163200), (492, 20121913728000), (493, 19940217292800), (494, 19134673689600), (495, 14230023808000), (496, 12811531622400), (497, 13147863321600), (498, 22298405068800), (499, 11832174950400), (500, 18674799091200), (501, 11176263705600), (502, 7996898246400), (503, 7905405715200), (507, 7468883251200), (508, 14238041932800), (509, 16521073288704), (510, 16727998694400), (511, 18935866775808), (512, 19240492723200), (513, 19395127987200), (514, 19549763251200), (515, 19080551347200), (516, 14512233164800), (517, 13430072678400), (518, 14102736076800), (519, 23589609523200), (520, 14801172019200), (521, 20638666944000), (522, 15517648742400)]
theorem block006_data : block006 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30929874548400 : Int) atom0336Coded) (CoefficientMerge.scale (27676226793600 : Int) atom0337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19355019465600 : Int) atom0338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14192212251600 : Int) atom0339Coded) (CoefficientMerge.scale (10448028259200 : Int) atom0340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22957537881600 : Int) atom0341Coded) (CoefficientMerge.scale (40599005328000 : Int) atom0342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32015781705600 : Int) atom0343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29965795171200 : Int) atom0344Coded) (CoefficientMerge.scale (21942260726400 : Int) atom0345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14664738614400 : Int) atom0346Coded) (CoefficientMerge.scale (12517241385600 : Int) atom0347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23040654336000 : Int) atom0348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39225167654400 : Int) atom0349Coded) (CoefficientMerge.scale (40376131084800 : Int) atom0350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34037154547200 : Int) atom0351Coded) (CoefficientMerge.scale (19513520611200 : Int) atom0352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20827437120000 : Int) atom0353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16982044692480 : Int) atom0354Coded) (CoefficientMerge.scale (33350960563200 : Int) atom0355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35187254323200 : Int) atom0356Coded) (CoefficientMerge.scale (20310858691200 : Int) atom0357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22313868595200 : Int) atom0358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17166447244800 : Int) atom0359Coded) (CoefficientMerge.scale (36337354099200 : Int) atom0360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20587269225600 : Int) atom0361Coded) (CoefficientMerge.scale (20398324262400 : Int) atom0362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18743726937600 : Int) atom0363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21384607305600 : Int) atom0364Coded) (CoefficientMerge.scale (21884755737600 : Int) atom0365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1655080560000 : Int) atom0366Coded) (CoefficientMerge.scale (2509440393600 : Int) atom0367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4803357888000 : Int) atom0368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4117163904000 : Int) atom0369Coded) (CoefficientMerge.scale (3430969920000 : Int) atom0370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4236153898752 : Int) atom0371Coded) (CoefficientMerge.scale (4003284902400 : Int) atom0372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4770887243904 : Int) atom0373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4586868518400 : Int) atom0374Coded) (CoefficientMerge.scale (4327854451200 : Int) atom0375Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4068840384000 : Int) atom0376Coded) (CoefficientMerge.scale (3497902732800 : Int) atom0377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (877411942400 : Int) atom0378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4103633318400 : Int) atom0379Coded) (CoefficientMerge.scale (393250636800 : Int) atom0380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9359299353600 : Int) atom0381Coded) (CoefficientMerge.scale (17682542438400 : Int) atom0382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16646486169600 : Int) atom0383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18593185826304 : Int) atom0384Coded) (CoefficientMerge.scale (18463779532800 : Int) atom0385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20335315915008 : Int) atom0386Coded) (CoefficientMerge.scale (20303610163200 : Int) atom0387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20121913728000 : Int) atom0388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19940217292800 : Int) atom0389Coded) (CoefficientMerge.scale (19134673689600 : Int) atom0390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14230023808000 : Int) atom0391Coded) (CoefficientMerge.scale (12811531622400 : Int) atom0392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13147863321600 : Int) atom0393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298405068800 : Int) atom0394Coded) (CoefficientMerge.scale (11832174950400 : Int) atom0395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18674799091200 : Int) atom0396Coded) (CoefficientMerge.scale (11176263705600 : Int) atom0397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996898246400 : Int) atom0398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7905405715200 : Int) atom0399Coded) (CoefficientMerge.scale (7468883251200 : Int) atom0400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14238041932800 : Int) atom0401Coded) (CoefficientMerge.scale (16521073288704 : Int) atom0402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16727998694400 : Int) atom0403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18935866775808 : Int) atom0404Coded) (CoefficientMerge.scale (19240492723200 : Int) atom0405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19395127987200 : Int) atom0406Coded) (CoefficientMerge.scale (19549763251200 : Int) atom0407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19080551347200 : Int) atom0408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14512233164800 : Int) atom0409Coded) (CoefficientMerge.scale (13430072678400 : Int) atom0410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14102736076800 : Int) atom0411Coded) (CoefficientMerge.scale (23589609523200 : Int) atom0412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14801172019200 : Int) atom0413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20638666944000 : Int) atom0414Coded) (CoefficientMerge.scale (15517648742400 : Int) atom0415Coded)))))))) := by decide +kernel
theorem block006_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block006 := by
  rw [block006_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0336Coded_nonneg g hg hA hB) (atom0337Coded_nonneg g hg hA hB)) (add_nonneg (atom0338Coded_nonneg g hg hA hB) (add_nonneg (atom0339Coded_nonneg g hg hA hB) (atom0340Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0341Coded_nonneg g hg hA hB) (atom0342Coded_nonneg g hg hA hB)) (add_nonneg (atom0343Coded_nonneg g hg hA hB) (add_nonneg (atom0344Coded_nonneg g hg hA hB) (atom0345Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0346Coded_nonneg g hg hA hB) (atom0347Coded_nonneg g hg hA hB)) (add_nonneg (atom0348Coded_nonneg g hg hA hB) (add_nonneg (atom0349Coded_nonneg g hg hA hB) (atom0350Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0351Coded_nonneg g hg hA hB) (atom0352Coded_nonneg g hg hA hB)) (add_nonneg (atom0353Coded_nonneg g hg hA hB) (add_nonneg (atom0354Coded_nonneg g hg hA hB) (atom0355Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0356Coded_nonneg g hg hA hB) (atom0357Coded_nonneg g hg hA hB)) (add_nonneg (atom0358Coded_nonneg g hg hA hB) (add_nonneg (atom0359Coded_nonneg g hg hA hB) (atom0360Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0361Coded_nonneg g hg hA hB) (atom0362Coded_nonneg g hg hA hB)) (add_nonneg (atom0363Coded_nonneg g hg hA hB) (add_nonneg (atom0364Coded_nonneg g hg hA hB) (atom0365Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0366Coded_nonneg g hg hA hB) (atom0367Coded_nonneg g hg hA hB)) (add_nonneg (atom0368Coded_nonneg g hg hA hB) (add_nonneg (atom0369Coded_nonneg g hg hA hB) (atom0370Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0371Coded_nonneg g hg hA hB) (atom0372Coded_nonneg g hg hA hB)) (add_nonneg (atom0373Coded_nonneg g hg hA hB) (add_nonneg (atom0374Coded_nonneg g hg hA hB) (atom0375Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0376Coded_nonneg g hg hA hB) (atom0377Coded_nonneg g hg hA hB)) (add_nonneg (atom0378Coded_nonneg g hg hA hB) (add_nonneg (atom0379Coded_nonneg g hg hA hB) (atom0380Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0381Coded_nonneg g hg hA hB) (atom0382Coded_nonneg g hg hA hB)) (add_nonneg (atom0383Coded_nonneg g hg hA hB) (add_nonneg (atom0384Coded_nonneg g hg hA hB) (atom0385Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0386Coded_nonneg g hg hA hB) (atom0387Coded_nonneg g hg hA hB)) (add_nonneg (atom0388Coded_nonneg g hg hA hB) (add_nonneg (atom0389Coded_nonneg g hg hA hB) (atom0390Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0391Coded_nonneg g hg hA hB) (atom0392Coded_nonneg g hg hA hB)) (add_nonneg (atom0393Coded_nonneg g hg hA hB) (add_nonneg (atom0394Coded_nonneg g hg hA hB) (atom0395Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0396Coded_nonneg g hg hA hB) (atom0397Coded_nonneg g hg hA hB)) (add_nonneg (atom0398Coded_nonneg g hg hA hB) (add_nonneg (atom0399Coded_nonneg g hg hA hB) (atom0400Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0401Coded_nonneg g hg hA hB) (atom0402Coded_nonneg g hg hA hB)) (add_nonneg (atom0403Coded_nonneg g hg hA hB) (add_nonneg (atom0404Coded_nonneg g hg hA hB) (atom0405Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0406Coded_nonneg g hg hA hB) (atom0407Coded_nonneg g hg hA hB)) (add_nonneg (atom0408Coded_nonneg g hg hA hB) (add_nonneg (atom0409Coded_nonneg g hg hA hB) (atom0410Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0411Coded_nonneg g hg hA hB) (atom0412Coded_nonneg g hg hA hB)) (add_nonneg (atom0413Coded_nonneg g hg hA hB) (add_nonneg (atom0414Coded_nonneg g hg hA hB) (atom0415Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
