import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0176 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0176 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5302217692800 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176Coded : CoefficientMerge.Poly := [(37, 1)]
theorem atom0176Coded_decode : atom0176 = SparsePolynomial.decodeCubic 21 atom0176Coded := by decide +kernel
theorem atom0176Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) := by
  have h := atom0176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0177 : SparsePolynomial.Poly := [([0,1,17], 1)]
theorem eval_atom0177 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1801017590400 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177Coded : CoefficientMerge.Poly := [(38, 1)]
theorem atom0177Coded_decode : atom0177 = SparsePolynomial.decodeCubic 21 atom0177Coded := by decide +kernel
theorem atom0177Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded) := by
  have h := atom0177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0178 : SparsePolynomial.Poly := [([0,1,18], 1)]
theorem eval_atom0178 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (787190140800 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178Coded : CoefficientMerge.Poly := [(39, 1)]
theorem atom0178Coded_decode : atom0178 = SparsePolynomial.decodeCubic 21 atom0178Coded := by decide +kernel
theorem atom0178Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) := by
  have h := atom0178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0179 : SparsePolynomial.Poly := [([0,1,19], 1)]
theorem eval_atom0179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (420253545600 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179Coded : CoefficientMerge.Poly := [(40, 1)]
theorem atom0179Coded_decode : atom0179 = SparsePolynomial.decodeCubic 21 atom0179Coded := by decide +kernel
theorem atom0179Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) := by
  have h := atom0179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0180 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0180 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7838074944000 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180Coded : CoefficientMerge.Poly := [(44, 1)]
theorem atom0180Coded_decode : atom0180 = SparsePolynomial.decodeCubic 21 atom0180Coded := by decide +kernel
theorem atom0180Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded) := by
  have h := atom0180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0181 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0181 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16012481587200 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181Coded : CoefficientMerge.Poly := [(45, 1)]
theorem atom0181Coded_decode : atom0181 = SparsePolynomial.decodeCubic 21 atom0181Coded := by decide +kernel
theorem atom0181Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) := by
  have h := atom0181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0182 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0182 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16348813286400 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182Coded : CoefficientMerge.Poly := [(46, 1)]
theorem atom0182Coded_decode : atom0182 = SparsePolynomial.decodeCubic 21 atom0182Coded := by decide +kernel
theorem atom0182Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded) := by
  have h := atom0182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0183 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16685144985600 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183Coded : CoefficientMerge.Poly := [(47, 1)]
theorem atom0183Coded_decode : atom0183 = SparsePolynomial.decodeCubic 21 atom0183Coded := by decide +kernel
theorem atom0183Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) := by
  have h := atom0183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0184 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0184 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17021476684800 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184Coded : CoefficientMerge.Poly := [(48, 1)]
theorem atom0184Coded_decode : atom0184 = SparsePolynomial.decodeCubic 21 atom0184Coded := by decide +kernel
theorem atom0184Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) := by
  have h := atom0184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0185 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0185 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17357808384000 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185Coded : CoefficientMerge.Poly := [(49, 1)]
theorem atom0185Coded_decode : atom0185 = SparsePolynomial.decodeCubic 21 atom0185Coded := by decide +kernel
theorem atom0185Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded) := by
  have h := atom0185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0186 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17694140083200 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186Coded : CoefficientMerge.Poly := [(50, 1)]
theorem atom0186Coded_decode : atom0186 = SparsePolynomial.decodeCubic 21 atom0186Coded := by decide +kernel
theorem atom0186Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) := by
  have h := atom0186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0187 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18030471782400 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187Coded : CoefficientMerge.Poly := [(51, 1)]
theorem atom0187Coded_decode : atom0187 = SparsePolynomial.decodeCubic 21 atom0187Coded := by decide +kernel
theorem atom0187Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded) := by
  have h := atom0187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0188 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18366803481600 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188Coded : CoefficientMerge.Poly := [(52, 1)]
theorem atom0188Coded_decode : atom0188 = SparsePolynomial.decodeCubic 21 atom0188Coded := by decide +kernel
theorem atom0188Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) := by
  have h := atom0188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0189 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18703135180800 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189Coded : CoefficientMerge.Poly := [(53, 1)]
theorem atom0189Coded_decode : atom0189 = SparsePolynomial.decodeCubic 21 atom0189Coded := by decide +kernel
theorem atom0189Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) := by
  have h := atom0189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0190 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19039466880000 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190Coded : CoefficientMerge.Poly := [(54, 1)]
theorem atom0190Coded_decode : atom0190 = SparsePolynomial.decodeCubic 21 atom0190Coded := by decide +kernel
theorem atom0190Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded) := by
  have h := atom0190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0191 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19375798579200 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191Coded : CoefficientMerge.Poly := [(55, 1)]
theorem atom0191Coded_decode : atom0191 = SparsePolynomial.decodeCubic 21 atom0191Coded := by decide +kernel
theorem atom0191Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) := by
  have h := atom0191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0192 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19712130278400 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192Coded : CoefficientMerge.Poly := [(56, 1)]
theorem atom0192Coded_decode : atom0192 = SparsePolynomial.decodeCubic 21 atom0192Coded := by decide +kernel
theorem atom0192Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded) := by
  have h := atom0192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0193 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22980733171200 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193Coded : CoefficientMerge.Poly := [(57, 1)]
theorem atom0193Coded_decode : atom0193 = SparsePolynomial.decodeCubic 21 atom0193Coded := by decide +kernel
theorem atom0193Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) := by
  have h := atom0193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0194 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0194 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13269638592000 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194Coded : CoefficientMerge.Poly := [(58, 1)]
theorem atom0194Coded_decode : atom0194 = SparsePolynomial.decodeCubic 21 atom0194Coded := by decide +kernel
theorem atom0194Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) := by
  have h := atom0194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0195 : SparsePolynomial.Poly := [([0,2,17], 1)]
theorem eval_atom0195 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10896850944000 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195Coded : CoefficientMerge.Poly := [(59, 1)]
theorem atom0195Coded_decode : atom0195 = SparsePolynomial.decodeCubic 21 atom0195Coded := by decide +kernel
theorem atom0195Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded) := by
  have h := atom0195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0196 : SparsePolynomial.Poly := [([0,2,18], 1)]
theorem eval_atom0196 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1702920844800 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196Coded : CoefficientMerge.Poly := [(60, 1)]
theorem atom0196Coded_decode : atom0196 = SparsePolynomial.decodeCubic 21 atom0196Coded := by decide +kernel
theorem atom0196Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) := by
  have h := atom0196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0197 : SparsePolynomial.Poly := [([0,2,19], 1)]
theorem eval_atom0197 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2888296790400 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197Coded : CoefficientMerge.Poly := [(61, 1)]
theorem atom0197Coded_decode : atom0197 = SparsePolynomial.decodeCubic 21 atom0197Coded := by decide +kernel
theorem atom0197Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded) := by
  have h := atom0197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0198 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0198 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7747226726400 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198Coded : CoefficientMerge.Poly := [(66, 1)]
theorem atom0198Coded_decode : atom0198 = SparsePolynomial.decodeCubic 21 atom0198Coded := by decide +kernel
theorem atom0198Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) := by
  have h := atom0198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0199 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0199 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15998951001600 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199Coded : CoefficientMerge.Poly := [(67, 1)]
theorem atom0199Coded_decode : atom0199 = SparsePolynomial.decodeCubic 21 atom0199Coded := by decide +kernel
theorem atom0199Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) := by
  have h := atom0199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0200 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0200 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16503448550400 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200Coded : CoefficientMerge.Poly := [(68, 1)]
theorem atom0200Coded_decode : atom0200 = SparsePolynomial.decodeCubic 21 atom0200Coded := by decide +kernel
theorem atom0200Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded) := by
  have h := atom0200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0201 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0201 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17007946099200 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201Coded : CoefficientMerge.Poly := [(69, 1)]
theorem atom0201Coded_decode : atom0201 = SparsePolynomial.decodeCubic 21 atom0201Coded := by decide +kernel
theorem atom0201Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) := by
  have h := atom0201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0202 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17512443648000 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202Coded : CoefficientMerge.Poly := [(70, 1)]
theorem atom0202Coded_decode : atom0202 = SparsePolynomial.decodeCubic 21 atom0202Coded := by decide +kernel
theorem atom0202Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded) := by
  have h := atom0202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0203 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0203 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18016941196800 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203Coded : CoefficientMerge.Poly := [(71, 1)]
theorem atom0203Coded_decode : atom0203 = SparsePolynomial.decodeCubic 21 atom0203Coded := by decide +kernel
theorem atom0203Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) := by
  have h := atom0203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0204 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0204 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18521438745600 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204Coded : CoefficientMerge.Poly := [(72, 1)]
theorem atom0204Coded_decode : atom0204 = SparsePolynomial.decodeCubic 21 atom0204Coded := by decide +kernel
theorem atom0204Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) := by
  have h := atom0204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0205 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0205 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19025936294400 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205Coded : CoefficientMerge.Poly := [(73, 1)]
theorem atom0205Coded_decode : atom0205 = SparsePolynomial.decodeCubic 21 atom0205Coded := by decide +kernel
theorem atom0205Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded) := by
  have h := atom0205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0206 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0206 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19530433843200 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206Coded : CoefficientMerge.Poly := [(74, 1)]
theorem atom0206Coded_decode : atom0206 = SparsePolynomial.decodeCubic 21 atom0206Coded := by decide +kernel
theorem atom0206Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) := by
  have h := atom0206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0207 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0207 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20034931392000 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207Coded : CoefficientMerge.Poly := [(75, 1)]
theorem atom0207Coded_decode : atom0207 = SparsePolynomial.decodeCubic 21 atom0207Coded := by decide +kernel
theorem atom0207Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded) := by
  have h := atom0207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0208 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0208 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20539428940800 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208Coded : CoefficientMerge.Poly := [(76, 1)]
theorem atom0208Coded_decode : atom0208 = SparsePolynomial.decodeCubic 21 atom0208Coded := by decide +kernel
theorem atom0208Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) := by
  have h := atom0208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0209 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0209 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21043926489600 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209Coded : CoefficientMerge.Poly := [(77, 1)]
theorem atom0209Coded_decode : atom0209 = SparsePolynomial.decodeCubic 21 atom0209Coded := by decide +kernel
theorem atom0209Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) := by
  have h := atom0209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0210 : SparsePolynomial.Poly := [([0,3,15], 1)]
theorem eval_atom0210 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24373900252800 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210Coded : CoefficientMerge.Poly := [(78, 1)]
theorem atom0210Coded_decode : atom0210 = SparsePolynomial.decodeCubic 21 atom0210Coded := by decide +kernel
theorem atom0210Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded) := by
  have h := atom0210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0211 : SparsePolynomial.Poly := [([0,3,16], 1)]
theorem eval_atom0211 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15288112022400 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211Coded : CoefficientMerge.Poly := [(79, 1)]
theorem atom0211Coded_decode : atom0211 = SparsePolynomial.decodeCubic 21 atom0211Coded := by decide +kernel
theorem atom0211Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) := by
  have h := atom0211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0212 : SparsePolynomial.Poly := [([0,3,17], 1)]
theorem eval_atom0212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11985579849600 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212Coded : CoefficientMerge.Poly := [(80, 1)]
theorem atom0212Coded_decode : atom0212 = SparsePolynomial.decodeCubic 21 atom0212Coded := by decide +kernel
theorem atom0212Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded) := by
  have h := atom0212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0213 : SparsePolynomial.Poly := [([0,3,18], 1)]
theorem eval_atom0213 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = ((g 0) * (g 3) * (g 18)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3766818384000 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213Coded : CoefficientMerge.Poly := [(81, 1)]
theorem atom0213Coded_decode : atom0213 = SparsePolynomial.decodeCubic 21 atom0213Coded := by decide +kernel
theorem atom0213Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) := by
  have h := atom0213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0214 : SparsePolynomial.Poly := [([0,3,19], 1)]
theorem eval_atom0214 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = ((g 0) * (g 3) * (g 19)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5075419305600 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214Coded : CoefficientMerge.Poly := [(82, 1)]
theorem atom0214Coded_decode : atom0214 = SparsePolynomial.decodeCubic 21 atom0214Coded := by decide +kernel
theorem atom0214Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) := by
  have h := atom0214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0215 : SparsePolynomial.Poly := [([0,3,20], 1)]
theorem eval_atom0215 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = ((g 0) * (g 3) * (g 20)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389970806400 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215Coded : CoefficientMerge.Poly := [(83, 1)]
theorem atom0215Coded_decode : atom0215 = SparsePolynomial.decodeCubic 21 atom0215Coded := by decide +kernel
theorem atom0215Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded) := by
  have h := atom0215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0216 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0216 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8898776208000 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216Coded : CoefficientMerge.Poly := [(88, 1)]
theorem atom0216Coded_decode : atom0216 = SparsePolynomial.decodeCubic 21 atom0216Coded := by decide +kernel
theorem atom0216Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) := by
  have h := atom0216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0217 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0217 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16329426810624 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217Coded : CoefficientMerge.Poly := [(89, 1)]
theorem atom0217Coded_decode : atom0217 = SparsePolynomial.decodeCubic 21 atom0217Coded := by decide +kernel
theorem atom0217Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded) := by
  have h := atom0217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0218 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0218 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16994415513600 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218Coded : CoefficientMerge.Poly := [(90, 1)]
theorem atom0218Coded_decode : atom0218 = SparsePolynomial.decodeCubic 21 atom0218Coded := by decide +kernel
theorem atom0218Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) := by
  have h := atom0218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0219 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0219 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17667078912000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219Coded : CoefficientMerge.Poly := [(91, 1)]
theorem atom0219Coded_decode : atom0219 = SparsePolynomial.decodeCubic 21 atom0219Coded := by decide +kernel
theorem atom0219Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) := by
  have h := atom0219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0220 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0220 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18339742310400 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220Coded : CoefficientMerge.Poly := [(92, 1)]
theorem atom0220Coded_decode : atom0220 = SparsePolynomial.decodeCubic 21 atom0220Coded := by decide +kernel
theorem atom0220Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded) := by
  have h := atom0220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0221 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0221 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19012405708800 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221Coded : CoefficientMerge.Poly := [(93, 1)]
theorem atom0221Coded_decode : atom0221 = SparsePolynomial.decodeCubic 21 atom0221Coded := by decide +kernel
theorem atom0221Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) := by
  have h := atom0221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0222 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0222 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19685069107200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222Coded : CoefficientMerge.Poly := [(94, 1)]
theorem atom0222Coded_decode : atom0222 = SparsePolynomial.decodeCubic 21 atom0222Coded := by decide +kernel
theorem atom0222Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded) := by
  have h := atom0222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0223 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0223 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20357732505600 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223Coded : CoefficientMerge.Poly := [(95, 1)]
theorem atom0223Coded_decode : atom0223 = SparsePolynomial.decodeCubic 21 atom0223Coded := by decide +kernel
theorem atom0223Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) := by
  have h := atom0223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0224 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0224 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21233148865600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224Coded : CoefficientMerge.Poly := [(96, 1)]
theorem atom0224Coded_decode : atom0224 = SparsePolynomial.decodeCubic 21 atom0224Coded := by decide +kernel
theorem atom0224Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) := by
  have h := atom0224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0225 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0225 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22067177025600 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225Coded : CoefficientMerge.Poly := [(97, 1)]
theorem atom0225Coded_decode : atom0225 = SparsePolynomial.decodeCubic 21 atom0225Coded := by decide +kernel
theorem atom0225Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded) := by
  have h := atom0225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0226 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0226 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22681852200000 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226Coded : CoefficientMerge.Poly := [(98, 1)]
theorem atom0226Coded_decode : atom0226 = SparsePolynomial.decodeCubic 21 atom0226Coded := by decide +kernel
theorem atom0226Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) := by
  have h := atom0226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0227 : SparsePolynomial.Poly := [([0,4,15], 1)]
theorem eval_atom0227 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25767067334400 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227Coded : CoefficientMerge.Poly := [(99, 1)]
theorem atom0227Coded_decode : atom0227 = SparsePolynomial.decodeCubic 21 atom0227Coded := by decide +kernel
theorem atom0227Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded) := by
  have h := atom0227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0228 : SparsePolynomial.Poly := [([0,4,16], 1)]
theorem eval_atom0228 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17557535532600 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228Coded : CoefficientMerge.Poly := [(100, 1)]
theorem atom0228Coded_decode : atom0228 = SparsePolynomial.decodeCubic 21 atom0228Coded := by decide +kernel
theorem atom0228Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) := by
  have h := atom0228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0229 : SparsePolynomial.Poly := [([0,4,17], 1)]
theorem eval_atom0229 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13074308755200 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229Coded : CoefficientMerge.Poly := [(101, 1)]
theorem atom0229Coded_decode : atom0229 = SparsePolynomial.decodeCubic 21 atom0229Coded := by decide +kernel
theorem atom0229Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) := by
  have h := atom0229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0230 : SparsePolynomial.Poly := [([0,4,18], 1)]
theorem eval_atom0230 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 0) * (g 4) * (g 18)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6011898921000 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230Coded : CoefficientMerge.Poly := [(102, 1)]
theorem atom0230Coded_decode : atom0230 = SparsePolynomial.decodeCubic 21 atom0230Coded := by decide +kernel
theorem atom0230Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded) := by
  have h := atom0230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0231 : SparsePolynomial.Poly := [([0,4,19], 1)]
theorem eval_atom0231 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 0) * (g 4) * (g 19)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7268672867400 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231Coded : CoefficientMerge.Poly := [(103, 1)]
theorem atom0231Coded_decode : atom0231 = SparsePolynomial.decodeCubic 21 atom0231Coded := by decide +kernel
theorem atom0231Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) := by
  have h := atom0231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0232 : SparsePolynomial.Poly := [([0,4,20], 1)]
theorem eval_atom0232 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 0) * (g 4) * (g 20)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2531397393000 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232Coded : CoefficientMerge.Poly := [(104, 1)]
theorem atom0232Coded_decode : atom0232 = SparsePolynomial.decodeCubic 21 atom0232Coded := by decide +kernel
theorem atom0232Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded) := by
  have h := atom0232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0233 : SparsePolynomial.Poly := [([0,5,5], 1)]
theorem eval_atom0233 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10430034421248 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(110, 1)]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 21 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([0,5,6], 1)]
theorem eval_atom0234 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18863725537728 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(111, 1)]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 21 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([0,5,7], 1)]
theorem eval_atom0235 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18055888573248 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(112, 1)]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 21 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([0,5,8], 1)]
theorem eval_atom0236 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18662543424000 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(113, 1)]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 21 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([0,5,9], 1)]
theorem eval_atom0237 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19685793960000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(114, 1)]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 21 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([0,5,10], 1)]
theorem eval_atom0238 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20344201920000 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(115, 1)]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 21 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([0,5,11], 1)]
theorem eval_atom0239 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21185031168000 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(116, 1)]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 21 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0240 : SparsePolynomial.Poly := [([0,5,12], 1)]
theorem eval_atom0240 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22373100702400 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240Coded : CoefficientMerge.Poly := [(117, 1)]
theorem atom0240Coded_decode : atom0240 = SparsePolynomial.decodeCubic 21 atom0240Coded := by decide +kernel
theorem atom0240Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded) := by
  have h := atom0240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0241 : SparsePolynomial.Poly := [([0,5,13], 1)]
theorem eval_atom0241 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23206404009600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241Coded : CoefficientMerge.Poly := [(118, 1)]
theorem atom0241Coded_decode : atom0241 = SparsePolynomial.decodeCubic 21 atom0241Coded := by decide +kernel
theorem atom0241Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) := by
  have h := atom0241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0242 : SparsePolynomial.Poly := [([0,5,14], 1)]
theorem eval_atom0242 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23885832700800 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242Coded : CoefficientMerge.Poly := [(119, 1)]
theorem atom0242Coded_decode : atom0242 = SparsePolynomial.decodeCubic 21 atom0242Coded := by decide +kernel
theorem atom0242Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded) := by
  have h := atom0242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0243 : SparsePolynomial.Poly := [([0,5,15], 1)]
theorem eval_atom0243 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27533078906688 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243Coded : CoefficientMerge.Poly := [(120, 1)]
theorem atom0243Coded_decode : atom0243 = SparsePolynomial.decodeCubic 21 atom0243Coded := by decide +kernel
theorem atom0243Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) := by
  have h := atom0243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0244 : SparsePolynomial.Poly := [([0,5,16], 1)]
theorem eval_atom0244 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19930254363648 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244Coded : CoefficientMerge.Poly := [(121, 1)]
theorem atom0244Coded_decode : atom0244 = SparsePolynomial.decodeCubic 21 atom0244Coded := by decide +kernel
theorem atom0244Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) := by
  have h := atom0244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0245 : SparsePolynomial.Poly := [([0,5,17], 1)]
theorem eval_atom0245 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16772949095616 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245Coded : CoefficientMerge.Poly := [(122, 1)]
theorem atom0245Coded_decode : atom0245 = SparsePolynomial.decodeCubic 21 atom0245Coded := by decide +kernel
theorem atom0245Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded) := by
  have h := atom0245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0246 : SparsePolynomial.Poly := [([0,5,18], 1)]
theorem eval_atom0246 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 0) * (g 5) * (g 18)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10592587378944 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246Coded : CoefficientMerge.Poly := [(123, 1)]
theorem atom0246Coded_decode : atom0246 = SparsePolynomial.decodeCubic 21 atom0246Coded := by decide +kernel
theorem atom0246Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) := by
  have h := atom0246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0247 : SparsePolynomial.Poly := [([0,5,19], 1)]
theorem eval_atom0247 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 0) * (g 5) * (g 19)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11062689626880 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247Coded : CoefficientMerge.Poly := [(124, 1)]
theorem atom0247Coded_decode : atom0247 = SparsePolynomial.decodeCubic 21 atom0247Coded := by decide +kernel
theorem atom0247Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded) := by
  have h := atom0247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0248 : SparsePolynomial.Poly := [([0,5,20], 1)]
theorem eval_atom0248 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 0) * (g 5) * (g 20)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7775809398144 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248Coded : CoefficientMerge.Poly := [(125, 1)]
theorem atom0248Coded_decode : atom0248 = SparsePolynomial.decodeCubic 21 atom0248Coded := by decide +kernel
theorem atom0248Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) := by
  have h := atom0248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0249 : SparsePolynomial.Poly := [([0,6,6], 1)]
theorem eval_atom0249 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13029789427200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249Coded : CoefficientMerge.Poly := [(132, 1)]
theorem atom0249Coded_decode : atom0249 = SparsePolynomial.decodeCubic 21 atom0249Coded := by decide +kernel
theorem atom0249Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) := by
  have h := atom0249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0250 : SparsePolynomial.Poly := [([0,6,7], 1)]
theorem eval_atom0250 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22027546931328 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250Coded : CoefficientMerge.Poly := [(133, 1)]
theorem atom0250Coded_decode : atom0250 = SparsePolynomial.decodeCubic 21 atom0250Coded := by decide +kernel
theorem atom0250Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded) := by
  have h := atom0250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0251 : SparsePolynomial.Poly := [([0,6,8], 1)]
theorem eval_atom0251 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20547763034400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251Coded : CoefficientMerge.Poly := [(134, 1)]
theorem atom0251Coded_decode : atom0251 = SparsePolynomial.decodeCubic 21 atom0251Coded := by decide +kernel
theorem atom0251Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) := by
  have h := atom0251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0252 : SparsePolynomial.Poly := [([0,6,9], 1)]
theorem eval_atom0252 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20553442761600 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252Coded : CoefficientMerge.Poly := [(135, 1)]
theorem atom0252Coded_decode : atom0252 = SparsePolynomial.decodeCubic 21 atom0252Coded := by decide +kernel
theorem atom0252Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded) := by
  have h := atom0252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0253 : SparsePolynomial.Poly := [([0,6,10], 1)]
theorem eval_atom0253 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21299316292800 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253Coded : CoefficientMerge.Poly := [(136, 1)]
theorem atom0253Coded_decode : atom0253 = SparsePolynomial.decodeCubic 21 atom0253Coded := by decide +kernel
theorem atom0253Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) := by
  have h := atom0253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0254 : SparsePolynomial.Poly := [([0,6,11], 1)]
theorem eval_atom0254 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22058417203200 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254Coded : CoefficientMerge.Poly := [(137, 1)]
theorem atom0254Coded_decode : atom0254 = SparsePolynomial.decodeCubic 21 atom0254Coded := by decide +kernel
theorem atom0254Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) := by
  have h := atom0254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0255 : SparsePolynomial.Poly := [([0,6,12], 1)]
theorem eval_atom0255 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0255 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0255_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23415680646400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255Coded : CoefficientMerge.Poly := [(138, 1)]
theorem atom0255Coded_decode : atom0255 = SparsePolynomial.decodeCubic 21 atom0255Coded := by decide +kernel
theorem atom0255Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded) := by
  have h := atom0255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block004 : CoefficientMerge.Poly := [(37, 5302217692800), (38, 1801017590400), (39, 787190140800), (40, 420253545600), (44, 7838074944000), (45, 16012481587200), (46, 16348813286400), (47, 16685144985600), (48, 17021476684800), (49, 17357808384000), (50, 17694140083200), (51, 18030471782400), (52, 18366803481600), (53, 18703135180800), (54, 19039466880000), (55, 19375798579200), (56, 19712130278400), (57, 22980733171200), (58, 13269638592000), (59, 10896850944000), (60, 1702920844800), (61, 2888296790400), (66, 7747226726400), (67, 15998951001600), (68, 16503448550400), (69, 17007946099200), (70, 17512443648000), (71, 18016941196800), (72, 18521438745600), (73, 19025936294400), (74, 19530433843200), (75, 20034931392000), (76, 20539428940800), (77, 21043926489600), (78, 24373900252800), (79, 15288112022400), (80, 11985579849600), (81, 3766818384000), (82, 5075419305600), (83, 389970806400), (88, 8898776208000), (89, 16329426810624), (90, 16994415513600), (91, 17667078912000), (92, 18339742310400), (93, 19012405708800), (94, 19685069107200), (95, 20357732505600), (96, 21233148865600), (97, 22067177025600), (98, 22681852200000), (99, 25767067334400), (100, 17557535532600), (101, 13074308755200), (102, 6011898921000), (103, 7268672867400), (104, 2531397393000), (110, 10430034421248), (111, 18863725537728), (112, 18055888573248), (113, 18662543424000), (114, 19685793960000), (115, 20344201920000), (116, 21185031168000), (117, 22373100702400), (118, 23206404009600), (119, 23885832700800), (120, 27533078906688), (121, 19930254363648), (122, 16772949095616), (123, 10592587378944), (124, 11062689626880), (125, 7775809398144), (132, 13029789427200), (133, 22027546931328), (134, 20547763034400), (135, 20553442761600), (136, 21299316292800), (137, 22058417203200), (138, 23415680646400)]
theorem block004_data : block004 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5302217692800 : Int) atom0176Coded) (CoefficientMerge.scale (1801017590400 : Int) atom0177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (787190140800 : Int) atom0178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (420253545600 : Int) atom0179Coded) (CoefficientMerge.scale (7838074944000 : Int) atom0180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16012481587200 : Int) atom0181Coded) (CoefficientMerge.scale (16348813286400 : Int) atom0182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16685144985600 : Int) atom0183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17021476684800 : Int) atom0184Coded) (CoefficientMerge.scale (17357808384000 : Int) atom0185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17694140083200 : Int) atom0186Coded) (CoefficientMerge.scale (18030471782400 : Int) atom0187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18366803481600 : Int) atom0188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18703135180800 : Int) atom0189Coded) (CoefficientMerge.scale (19039466880000 : Int) atom0190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19375798579200 : Int) atom0191Coded) (CoefficientMerge.scale (19712130278400 : Int) atom0192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22980733171200 : Int) atom0193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269638592000 : Int) atom0194Coded) (CoefficientMerge.scale (10896850944000 : Int) atom0195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1702920844800 : Int) atom0196Coded) (CoefficientMerge.scale (2888296790400 : Int) atom0197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7747226726400 : Int) atom0198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15998951001600 : Int) atom0199Coded) (CoefficientMerge.scale (16503448550400 : Int) atom0200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17007946099200 : Int) atom0201Coded) (CoefficientMerge.scale (17512443648000 : Int) atom0202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18016941196800 : Int) atom0203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18521438745600 : Int) atom0204Coded) (CoefficientMerge.scale (19025936294400 : Int) atom0205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19530433843200 : Int) atom0206Coded) (CoefficientMerge.scale (20034931392000 : Int) atom0207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20539428940800 : Int) atom0208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21043926489600 : Int) atom0209Coded) (CoefficientMerge.scale (24373900252800 : Int) atom0210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15288112022400 : Int) atom0211Coded) (CoefficientMerge.scale (11985579849600 : Int) atom0212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3766818384000 : Int) atom0213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5075419305600 : Int) atom0214Coded) (CoefficientMerge.scale (389970806400 : Int) atom0215Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8898776208000 : Int) atom0216Coded) (CoefficientMerge.scale (16329426810624 : Int) atom0217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16994415513600 : Int) atom0218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17667078912000 : Int) atom0219Coded) (CoefficientMerge.scale (18339742310400 : Int) atom0220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19012405708800 : Int) atom0221Coded) (CoefficientMerge.scale (19685069107200 : Int) atom0222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20357732505600 : Int) atom0223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21233148865600 : Int) atom0224Coded) (CoefficientMerge.scale (22067177025600 : Int) atom0225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22681852200000 : Int) atom0226Coded) (CoefficientMerge.scale (25767067334400 : Int) atom0227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17557535532600 : Int) atom0228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13074308755200 : Int) atom0229Coded) (CoefficientMerge.scale (6011898921000 : Int) atom0230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7268672867400 : Int) atom0231Coded) (CoefficientMerge.scale (2531397393000 : Int) atom0232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10430034421248 : Int) atom0233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18863725537728 : Int) atom0234Coded) (CoefficientMerge.scale (18055888573248 : Int) atom0235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18662543424000 : Int) atom0236Coded) (CoefficientMerge.scale (19685793960000 : Int) atom0237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20344201920000 : Int) atom0238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21185031168000 : Int) atom0239Coded) (CoefficientMerge.scale (22373100702400 : Int) atom0240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23206404009600 : Int) atom0241Coded) (CoefficientMerge.scale (23885832700800 : Int) atom0242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27533078906688 : Int) atom0243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19930254363648 : Int) atom0244Coded) (CoefficientMerge.scale (16772949095616 : Int) atom0245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10592587378944 : Int) atom0246Coded) (CoefficientMerge.scale (11062689626880 : Int) atom0247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7775809398144 : Int) atom0248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13029789427200 : Int) atom0249Coded) (CoefficientMerge.scale (22027546931328 : Int) atom0250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20547763034400 : Int) atom0251Coded) (CoefficientMerge.scale (20553442761600 : Int) atom0252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21299316292800 : Int) atom0253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22058417203200 : Int) atom0254Coded) (CoefficientMerge.scale (23415680646400 : Int) atom0255Coded)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block004 := by
  rw [block004_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0176Coded_nonneg g hg hA hB) (atom0177Coded_nonneg g hg hA hB)) (add_nonneg (atom0178Coded_nonneg g hg hA hB) (add_nonneg (atom0179Coded_nonneg g hg hA hB) (atom0180Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0181Coded_nonneg g hg hA hB) (atom0182Coded_nonneg g hg hA hB)) (add_nonneg (atom0183Coded_nonneg g hg hA hB) (add_nonneg (atom0184Coded_nonneg g hg hA hB) (atom0185Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0186Coded_nonneg g hg hA hB) (atom0187Coded_nonneg g hg hA hB)) (add_nonneg (atom0188Coded_nonneg g hg hA hB) (add_nonneg (atom0189Coded_nonneg g hg hA hB) (atom0190Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0191Coded_nonneg g hg hA hB) (atom0192Coded_nonneg g hg hA hB)) (add_nonneg (atom0193Coded_nonneg g hg hA hB) (add_nonneg (atom0194Coded_nonneg g hg hA hB) (atom0195Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0196Coded_nonneg g hg hA hB) (atom0197Coded_nonneg g hg hA hB)) (add_nonneg (atom0198Coded_nonneg g hg hA hB) (add_nonneg (atom0199Coded_nonneg g hg hA hB) (atom0200Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0201Coded_nonneg g hg hA hB) (atom0202Coded_nonneg g hg hA hB)) (add_nonneg (atom0203Coded_nonneg g hg hA hB) (add_nonneg (atom0204Coded_nonneg g hg hA hB) (atom0205Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0206Coded_nonneg g hg hA hB) (atom0207Coded_nonneg g hg hA hB)) (add_nonneg (atom0208Coded_nonneg g hg hA hB) (add_nonneg (atom0209Coded_nonneg g hg hA hB) (atom0210Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0211Coded_nonneg g hg hA hB) (atom0212Coded_nonneg g hg hA hB)) (add_nonneg (atom0213Coded_nonneg g hg hA hB) (add_nonneg (atom0214Coded_nonneg g hg hA hB) (atom0215Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0216Coded_nonneg g hg hA hB) (atom0217Coded_nonneg g hg hA hB)) (add_nonneg (atom0218Coded_nonneg g hg hA hB) (add_nonneg (atom0219Coded_nonneg g hg hA hB) (atom0220Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0221Coded_nonneg g hg hA hB) (atom0222Coded_nonneg g hg hA hB)) (add_nonneg (atom0223Coded_nonneg g hg hA hB) (add_nonneg (atom0224Coded_nonneg g hg hA hB) (atom0225Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0226Coded_nonneg g hg hA hB) (atom0227Coded_nonneg g hg hA hB)) (add_nonneg (atom0228Coded_nonneg g hg hA hB) (add_nonneg (atom0229Coded_nonneg g hg hA hB) (atom0230Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0231Coded_nonneg g hg hA hB) (atom0232Coded_nonneg g hg hA hB)) (add_nonneg (atom0233Coded_nonneg g hg hA hB) (add_nonneg (atom0234Coded_nonneg g hg hA hB) (atom0235Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0236Coded_nonneg g hg hA hB) (atom0237Coded_nonneg g hg hA hB)) (add_nonneg (atom0238Coded_nonneg g hg hA hB) (add_nonneg (atom0239Coded_nonneg g hg hA hB) (atom0240Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0241Coded_nonneg g hg hA hB) (atom0242Coded_nonneg g hg hA hB)) (add_nonneg (atom0243Coded_nonneg g hg hA hB) (add_nonneg (atom0244Coded_nonneg g hg hA hB) (atom0245Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0246Coded_nonneg g hg hA hB) (atom0247Coded_nonneg g hg hA hB)) (add_nonneg (atom0248Coded_nonneg g hg hA hB) (add_nonneg (atom0249Coded_nonneg g hg hA hB) (atom0250Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0251Coded_nonneg g hg hA hB) (atom0252Coded_nonneg g hg hA hB)) (add_nonneg (atom0253Coded_nonneg g hg hA hB) (add_nonneg (atom0254Coded_nonneg g hg hA hB) (atom0255Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
