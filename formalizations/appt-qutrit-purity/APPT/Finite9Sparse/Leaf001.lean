import APPT.Finite9Sparse.Base00
import APPT.Finite9Sparse.Base01
import APPT.Finite9Sparse.Base02
import APPT.Finite9Sparse.Base03
import APPT.Finite9Sparse.Base04
import APPT.Finite9Sparse.Base05
import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0080 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0080 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (297000 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080Coded : CoefficientMerge.Poly := [(196, 1)]
theorem atom0080Coded_decode : atom0080 = SparsePolynomial.decodeCubic 9 atom0080Coded := by decide +kernel
theorem atom0080Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (297000 : Int) atom0080Coded) := by
  have h := atom0080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0081 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0081 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (922320 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081Coded : CoefficientMerge.Poly := [(197, 1)]
theorem atom0081Coded_decode : atom0081 = SparsePolynomial.decodeCubic 9 atom0081Coded := by decide +kernel
theorem atom0081Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (922320 : Int) atom0081Coded) := by
  have h := atom0081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0082 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0082 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262368 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082Coded : CoefficientMerge.Poly := [(202, 1)]
theorem atom0082Coded_decode : atom0082 = SparsePolynomial.decodeCubic 9 atom0082Coded := by decide +kernel
theorem atom0082Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (262368 : Int) atom0082Coded) := by
  have h := atom0082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0083 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0083 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (692820 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083Coded : CoefficientMerge.Poly := [(203, 1)]
theorem atom0083Coded_decode : atom0083 = SparsePolynomial.decodeCubic 9 atom0083Coded := by decide +kernel
theorem atom0083Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (692820 : Int) atom0083Coded) := by
  have h := atom0083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0084 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0084 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1045440 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084Coded : CoefficientMerge.Poly := [(204, 1)]
theorem atom0084Coded_decode : atom0084 = SparsePolynomial.decodeCubic 9 atom0084Coded := by decide +kernel
theorem atom0084Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1045440 : Int) atom0084Coded) := by
  have h := atom0084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0085 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0085 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (635040 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085Coded : CoefficientMerge.Poly := [(205, 1)]
theorem atom0085Coded_decode : atom0085 = SparsePolynomial.decodeCubic 9 atom0085Coded := by decide +kernel
theorem atom0085Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (635040 : Int) atom0085Coded) := by
  have h := atom0085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0086 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0086 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (924480 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086Coded : CoefficientMerge.Poly := [(206, 1)]
theorem atom0086Coded_decode : atom0086 = SparsePolynomial.decodeCubic 9 atom0086Coded := by decide +kernel
theorem atom0086Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (924480 : Int) atom0086Coded) := by
  have h := atom0086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0087 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0087 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (500580 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087Coded : CoefficientMerge.Poly := [(212, 1)]
theorem atom0087Coded_decode : atom0087 = SparsePolynomial.decodeCubic 9 atom0087Coded := by decide +kernel
theorem atom0087Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (500580 : Int) atom0087Coded) := by
  have h := atom0087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0088 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0088 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (997380 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088Coded : CoefficientMerge.Poly := [(213, 1)]
theorem atom0088Coded_decode : atom0088 = SparsePolynomial.decodeCubic 9 atom0088Coded := by decide +kernel
theorem atom0088Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (997380 : Int) atom0088Coded) := by
  have h := atom0088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0089 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0089 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (775440 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089Coded : CoefficientMerge.Poly := [(214, 1)]
theorem atom0089Coded_decode : atom0089 = SparsePolynomial.decodeCubic 9 atom0089Coded := by decide +kernel
theorem atom0089Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (775440 : Int) atom0089Coded) := by
  have h := atom0089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0090 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0090 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1195560 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090Coded : CoefficientMerge.Poly := [(215, 1)]
theorem atom0090Coded_decode : atom0090 = SparsePolynomial.decodeCubic 9 atom0090Coded := by decide +kernel
theorem atom0090Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1195560 : Int) atom0090Coded) := by
  have h := atom0090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0091 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0091 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (421200 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091Coded : CoefficientMerge.Poly := [(222, 1)]
theorem atom0091Coded_decode : atom0091 = SparsePolynomial.decodeCubic 9 atom0091Coded := by decide +kernel
theorem atom0091Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (421200 : Int) atom0091Coded) := by
  have h := atom0091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0092 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0092 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854820 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092Coded : CoefficientMerge.Poly := [(223, 1)]
theorem atom0092Coded_decode : atom0092 = SparsePolynomial.decodeCubic 9 atom0092Coded := by decide +kernel
theorem atom0092Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (854820 : Int) atom0092Coded) := by
  have h := atom0092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0093 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0093 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1395360 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093Coded : CoefficientMerge.Poly := [(224, 1)]
theorem atom0093Coded_decode : atom0093 = SparsePolynomial.decodeCubic 9 atom0093Coded := by decide +kernel
theorem atom0093Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1395360 : Int) atom0093Coded) := by
  have h := atom0093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0094 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0094 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347760 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094Coded : CoefficientMerge.Poly := [(232, 1)]
theorem atom0094Coded_decode : atom0094 = SparsePolynomial.decodeCubic 9 atom0094Coded := by decide +kernel
theorem atom0094Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (347760 : Int) atom0094Coded) := by
  have h := atom0094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0095 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0095 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1351350 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095Coded : CoefficientMerge.Poly := [(233, 1)]
theorem atom0095Coded_decode : atom0095 = SparsePolynomial.decodeCubic 9 atom0095Coded := by decide +kernel
theorem atom0095Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1351350 : Int) atom0095Coded) := by
  have h := atom0095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0096 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0096 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (933120 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096Coded : CoefficientMerge.Poly := [(242, 1)]
theorem atom0096Coded_decode : atom0096 = SparsePolynomial.decodeCubic 9 atom0096Coded := by decide +kernel
theorem atom0096Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (933120 : Int) atom0096Coded) := by
  have h := atom0096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0097 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0097 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161280 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097Coded : CoefficientMerge.Poly := [(273, 1)]
theorem atom0097Coded_decode : atom0097 = SparsePolynomial.decodeCubic 9 atom0097Coded := by decide +kernel
theorem atom0097Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (161280 : Int) atom0097Coded) := by
  have h := atom0097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0098 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0098 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370080 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098Coded : CoefficientMerge.Poly := [(274, 1)]
theorem atom0098Coded_decode : atom0098 = SparsePolynomial.decodeCubic 9 atom0098Coded := by decide +kernel
theorem atom0098Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (370080 : Int) atom0098Coded) := by
  have h := atom0098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0099 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0099 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (525240 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099Coded : CoefficientMerge.Poly := [(275, 1)]
theorem atom0099Coded_decode : atom0099 = SparsePolynomial.decodeCubic 9 atom0099Coded := by decide +kernel
theorem atom0099Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (525240 : Int) atom0099Coded) := by
  have h := atom0099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0100 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0100 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (609120 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100Coded : CoefficientMerge.Poly := [(276, 1)]
theorem atom0100Coded_decode : atom0100 = SparsePolynomial.decodeCubic 9 atom0100Coded := by decide +kernel
theorem atom0100Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (609120 : Int) atom0100Coded) := by
  have h := atom0100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0101 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0101 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28800 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101Coded : CoefficientMerge.Poly := [(277, 1)]
theorem atom0101Coded_decode : atom0101 = SparsePolynomial.decodeCubic 9 atom0101Coded := by decide +kernel
theorem atom0101Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (28800 : Int) atom0101Coded) := by
  have h := atom0101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0102 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0102 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (381600 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102Coded : CoefficientMerge.Poly := [(278, 1)]
theorem atom0102Coded_decode : atom0102 = SparsePolynomial.decodeCubic 9 atom0102Coded := by decide +kernel
theorem atom0102Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (381600 : Int) atom0102Coded) := by
  have h := atom0102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0103 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0103 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283032 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103Coded : CoefficientMerge.Poly := [(283, 1)]
theorem atom0103Coded_decode : atom0103 = SparsePolynomial.decodeCubic 9 atom0103Coded := by decide +kernel
theorem atom0103Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (283032 : Int) atom0103Coded) := by
  have h := atom0103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0104 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0104 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (867060 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104Coded : CoefficientMerge.Poly := [(284, 1)]
theorem atom0104Coded_decode : atom0104 = SparsePolynomial.decodeCubic 9 atom0104Coded := by decide +kernel
theorem atom0104Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (867060 : Int) atom0104Coded) := by
  have h := atom0104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0105 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0105 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1316160 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105Coded : CoefficientMerge.Poly := [(285, 1)]
theorem atom0105Coded_decode : atom0105 = SparsePolynomial.decodeCubic 9 atom0105Coded := by decide +kernel
theorem atom0105Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1316160 : Int) atom0105Coded) := by
  have h := atom0105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0106 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0106 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (535680 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106Coded : CoefficientMerge.Poly := [(286, 1)]
theorem atom0106Coded_decode : atom0106 = SparsePolynomial.decodeCubic 9 atom0106Coded := by decide +kernel
theorem atom0106Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (535680 : Int) atom0106Coded) := by
  have h := atom0106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0107 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0107 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (921600 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107Coded : CoefficientMerge.Poly := [(287, 1)]
theorem atom0107Coded_decode : atom0107 = SparsePolynomial.decodeCubic 9 atom0107Coded := by decide +kernel
theorem atom0107Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (921600 : Int) atom0107Coded) := by
  have h := atom0107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0108 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0108 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (610740 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108Coded : CoefficientMerge.Poly := [(293, 1)]
theorem atom0108Coded_decode : atom0108 = SparsePolynomial.decodeCubic 9 atom0108Coded := by decide +kernel
theorem atom0108Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (610740 : Int) atom0108Coded) := by
  have h := atom0108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0109 : SparsePolynomial.Poly := [([3,5,6], 1)]
theorem eval_atom0109 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1350900 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109Coded : CoefficientMerge.Poly := [(294, 1)]
theorem atom0109Coded_decode : atom0109 = SparsePolynomial.decodeCubic 9 atom0109Coded := by decide +kernel
theorem atom0109Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1350900 : Int) atom0109Coded) := by
  have h := atom0109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0110 : SparsePolynomial.Poly := [([3,5,7], 1)]
theorem eval_atom0110 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (816120 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110Coded : CoefficientMerge.Poly := [(295, 1)]
theorem atom0110Coded_decode : atom0110 = SparsePolynomial.decodeCubic 9 atom0110Coded := by decide +kernel
theorem atom0110Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (816120 : Int) atom0110Coded) := by
  have h := atom0110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0111 : SparsePolynomial.Poly := [([3,5,8], 1)]
theorem eval_atom0111 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (811080 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111Coded : CoefficientMerge.Poly := [(296, 1)]
theorem atom0111Coded_decode : atom0111 = SparsePolynomial.decodeCubic 9 atom0111Coded := by decide +kernel
theorem atom0111Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (811080 : Int) atom0111Coded) := by
  have h := atom0111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0112 : SparsePolynomial.Poly := [([3,6,6], 1)]
theorem eval_atom0112 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (639360 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112Coded : CoefficientMerge.Poly := [(303, 1)]
theorem atom0112Coded_decode : atom0112 = SparsePolynomial.decodeCubic 9 atom0112Coded := by decide +kernel
theorem atom0112Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (639360 : Int) atom0112Coded) := by
  have h := atom0112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0113 : SparsePolynomial.Poly := [([3,6,7], 1)]
theorem eval_atom0113 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1025280 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113Coded : CoefficientMerge.Poly := [(304, 1)]
theorem atom0113Coded_decode : atom0113 = SparsePolynomial.decodeCubic 9 atom0113Coded := by decide +kernel
theorem atom0113Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1025280 : Int) atom0113Coded) := by
  have h := atom0113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0114 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom0114 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (771840 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114Coded : CoefficientMerge.Poly := [(305, 1)]
theorem atom0114Coded_decode : atom0114 = SparsePolynomial.decodeCubic 9 atom0114Coded := by decide +kernel
theorem atom0114Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (771840 : Int) atom0114Coded) := by
  have h := atom0114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0115 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom0115 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (518400 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115Coded : CoefficientMerge.Poly := [(313, 1)]
theorem atom0115Coded_decode : atom0115 = SparsePolynomial.decodeCubic 9 atom0115Coded := by decide +kernel
theorem atom0115Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (518400 : Int) atom0115Coded) := by
  have h := atom0115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0116 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom0116 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (930240 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116Coded : CoefficientMerge.Poly := [(314, 1)]
theorem atom0116Coded_decode : atom0116 = SparsePolynomial.decodeCubic 9 atom0116Coded := by decide +kernel
theorem atom0116Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (930240 : Int) atom0116Coded) := by
  have h := atom0116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0117 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom0117 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311040 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117Coded : CoefficientMerge.Poly := [(323, 1)]
theorem atom0117Coded_decode : atom0117 = SparsePolynomial.decodeCubic 9 atom0117Coded := by decide +kernel
theorem atom0117Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (311040 : Int) atom0117Coded) := by
  have h := atom0117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0118 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0118 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118Coded : CoefficientMerge.Poly := [(364, 1)]
theorem atom0118Coded_decode : atom0118 = SparsePolynomial.decodeCubic 9 atom0118Coded := by decide +kernel
theorem atom0118Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (360 : Int) atom0118Coded) := by
  have h := atom0118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0119 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom0119 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121716 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119Coded : CoefficientMerge.Poly := [(365, 1)]
theorem atom0119Coded_decode : atom0119 = SparsePolynomial.decodeCubic 9 atom0119Coded := by decide +kernel
theorem atom0119Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (121716 : Int) atom0119Coded) := by
  have h := atom0119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0120 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0120 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (425304 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120Coded : CoefficientMerge.Poly := [(366, 1)]
theorem atom0120Coded_decode : atom0120 = SparsePolynomial.decodeCubic 9 atom0120Coded := by decide +kernel
theorem atom0120Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (425304 : Int) atom0120Coded) := by
  have h := atom0120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0121 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom0121 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127080 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121Coded : CoefficientMerge.Poly := [(367, 1)]
theorem atom0121Coded_decode : atom0121 = SparsePolynomial.decodeCubic 9 atom0121Coded := by decide +kernel
theorem atom0121Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (127080 : Int) atom0121Coded) := by
  have h := atom0121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0122 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0122 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (295416 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122Coded : CoefficientMerge.Poly := [(368, 1)]
theorem atom0122Coded_decode : atom0122 = SparsePolynomial.decodeCubic 9 atom0122Coded := by decide +kernel
theorem atom0122Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (295416 : Int) atom0122Coded) := by
  have h := atom0122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0123 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0123 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353160 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123Coded : CoefficientMerge.Poly := [(374, 1)]
theorem atom0123Coded_decode : atom0123 = SparsePolynomial.decodeCubic 9 atom0123Coded := by decide +kernel
theorem atom0123Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (353160 : Int) atom0123Coded) := by
  have h := atom0123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0124 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0124 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1103400 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124Coded : CoefficientMerge.Poly := [(375, 1)]
theorem atom0124Coded_decode : atom0124 = SparsePolynomial.decodeCubic 9 atom0124Coded := by decide +kernel
theorem atom0124Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1103400 : Int) atom0124Coded) := by
  have h := atom0124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0125 : SparsePolynomial.Poly := [([4,5,7], 1)]
theorem eval_atom0125 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (836280 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125Coded : CoefficientMerge.Poly := [(376, 1)]
theorem atom0125Coded_decode : atom0125 = SparsePolynomial.decodeCubic 9 atom0125Coded := by decide +kernel
theorem atom0125Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (836280 : Int) atom0125Coded) := by
  have h := atom0125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0126 : SparsePolynomial.Poly := [([4,5,8], 1)]
theorem eval_atom0126 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (964440 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126Coded : CoefficientMerge.Poly := [(377, 1)]
theorem atom0126Coded_decode : atom0126 = SparsePolynomial.decodeCubic 9 atom0126Coded := by decide +kernel
theorem atom0126Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (964440 : Int) atom0126Coded) := by
  have h := atom0126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0127 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0127 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (624240 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127Coded : CoefficientMerge.Poly := [(384, 1)]
theorem atom0127Coded_decode : atom0127 = SparsePolynomial.decodeCubic 9 atom0127Coded := by decide +kernel
theorem atom0127Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (624240 : Int) atom0127Coded) := by
  have h := atom0127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0128 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0128 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1164960 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128Coded : CoefficientMerge.Poly := [(385, 1)]
theorem atom0128Coded_decode : atom0128 = SparsePolynomial.decodeCubic 9 atom0128Coded := by decide +kernel
theorem atom0128Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1164960 : Int) atom0128Coded) := by
  have h := atom0128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0129 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0129 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1081440 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(386, 1)]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 9 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1081440 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0130 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (648000 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(394, 1)]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 9 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (648000 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0131 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1396080 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(395, 1)]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 9 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1396080 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0132 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (622080 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(404, 1)]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 9 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (622080 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom0133 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121500 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(455, 1)]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 9 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (121500 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom0134 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (495180 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(456, 1)]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 9 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (495180 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom0135 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (428220 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(457, 1)]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 9 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (428220 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom0136 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289980 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(458, 1)]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 9 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (289980 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom0137 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (609120 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(465, 1)]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 9 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (609120 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([5,6,7], 1)]
theorem eval_atom0138 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1304640 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(466, 1)]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 9 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1304640 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([5,6,8], 1)]
theorem eval_atom0139 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853200 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(467, 1)]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 9 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (853200 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom0140 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (777600 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(475, 1)]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 9 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (777600 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([5,7,8], 1)]
theorem eval_atom0141 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1324080 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(476, 1)]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 9 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1324080 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom0142 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (395280 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(485, 1)]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 9 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (395280 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom0143 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198000 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(546, 1)]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 9 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (198000 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom0144 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (722160 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(547, 1)]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 9 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (722160 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom0145 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (383760 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(548, 1)]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 9 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (383760 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom0146 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (907200 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(556, 1)]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 9 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (907200 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([6,7,8], 1)]
theorem eval_atom0147 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1394640 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(557, 1)]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 9 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (1394640 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom0148 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (311040 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(566, 1)]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 9 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (311040 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom0149 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345600 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(637, 1)]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 9 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (345600 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom0150 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (930240 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(638, 1)]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 9 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (930240 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom0151 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (622080 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(647, 1)]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 9 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (622080 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -4), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -8), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -6), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -10), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -4), ([1,5,6], -8), ([1,5,7], -4), ([1,5,8], -4), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -4), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -10), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -4), ([2,5,6], -8), ([2,5,7], -4), ([2,5,8], -4), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -8), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -14), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -6), ([3,5,6], -12), ([3,5,7], -4), ([3,5,8], -4), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -6), ([4,5,6], -12), ([4,5,7], -4), ([4,5,8], -4), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -2), ([5,5,6], -6), ([5,5,7], -2), ([5,5,8], -2), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 4), ([5,7,8], 8), ([5,8,8], 8), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [] 1 base00 := by decide +kernel
theorem eval_atom0152 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = (detA (outer g)) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49410 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (detA (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(3, -2), (4, -2), (5, -2), (6, -2), (7, -2), (8, -2), (11, -2), (12, -6), (13, -4), (14, -4), (15, -4), (16, -4), (17, -4), (20, -2), (21, -8), (22, -6), (23, -4), (24, -4), (25, -4), (26, -4), (30, -6), (31, -10), (32, -8), (33, -8), (34, -4), (35, -4), (40, -4), (41, -8), (42, -8), (43, -4), (44, -4), (50, -4), (51, -8), (52, -4), (53, -4), (60, -4), (61, -4), (62, -4), (92, -2), (93, -4), (94, -2), (95, -2), (96, -4), (97, -4), (98, -4), (101, -4), (102, -12), (103, -8), (104, -6), (105, -10), (106, -8), (107, -8), (111, -8), (112, -12), (113, -10), (114, -14), (115, -8), (116, -8), (121, -4), (122, -8), (123, -12), (124, -8), (125, -8), (131, -4), (132, -8), (133, -4), (134, -4), (141, -4), (142, -4), (143, -4), (182, -2), (183, -8), (184, -6), (185, -4), (186, -6), (187, -4), (188, -6), (192, -10), (193, -16), (194, -12), (195, -16), (196, -8), (197, -12), (202, -6), (203, -10), (204, -14), (205, -8), (206, -8), (212, -4), (213, -8), (214, -4), (215, -4), (222, -4), (223, -4), (224, -4), (273, -4), (274, -10), (275, -8), (276, -10), (277, -4), (278, -6), (283, -8), (284, -14), (285, -18), (286, -8), (287, -8), (293, -6), (294, -12), (295, -4), (296, -4), (303, -6), (304, -4), (305, 4), (314, 8), (323, 8), (364, -2), (365, -6), (366, -8), (367, -4), (368, -4), (374, -6), (375, -12), (376, -4), (377, -4), (384, -6), (385, -4), (386, 4), (395, 8), (404, 8), (455, -2), (456, -6), (457, -2), (458, -2), (465, -6), (466, -4), (467, 4), (476, 8), (485, 8), (546, -2), (547, -2), (548, 6), (557, 16), (566, 16), (638, 8), (647, 16), (728, 8)]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 9 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (49410 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0153 : SparsePolynomial.Poly := [([0,1,4], -4), ([1,1,4], -12), ([1,2,4], -16), ([1,3,4], -8), ([1,4,4], -4), ([1,4,5], 4), ([1,4,6], 6), ([1,4,7], 10), ([1,4,8], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [1,4] 1 base01 := by decide +kernel
theorem eval_atom0153 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = (quadA (outer g) ![2,1,2] * g 1 * g 4) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6575 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153Coded : CoefficientMerge.Poly := [(13, -4), (94, -12), (103, -16), (112, -8), (121, -4), (122, 4), (123, 6), (124, 10), (125, 18)]
theorem atom0153Coded_decode : atom0153 = SparsePolynomial.decodeCubic 9 atom0153Coded := by decide +kernel
theorem atom0153Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (6575 : Int) atom0153Coded) := by
  have h := atom0153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0154 : SparsePolynomial.Poly := [([0,1,7], -4), ([1,1,7], -12), ([1,2,7], -16), ([1,3,7], -8), ([1,4,7], -4), ([1,5,7], 4), ([1,6,7], 6), ([1,7,7], 10), ([1,7,8], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [1,7] 1 base01 := by decide +kernel
theorem eval_atom0154 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = (quadA (outer g) ![2,1,2] * g 1 * g 7) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8005 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154Coded : CoefficientMerge.Poly := [(16, -4), (97, -12), (106, -16), (115, -8), (124, -4), (133, 4), (142, 6), (151, 10), (152, 18)]
theorem atom0154Coded_decode : atom0154 = SparsePolynomial.decodeCubic 9 atom0154Coded := by decide +kernel
theorem atom0154Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (8005 : Int) atom0154Coded) := by
  have h := atom0154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0155 : SparsePolynomial.Poly := [([0,1,8], -4), ([1,1,8], -12), ([1,2,8], -16), ([1,3,8], -8), ([1,4,8], -4), ([1,5,8], 4), ([1,6,8], 6), ([1,7,8], 10), ([1,8,8], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [1,8] 1 base01 := by decide +kernel
theorem eval_atom0155 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = (quadA (outer g) ![2,1,2] * g 1 * g 8) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15915 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155Coded : CoefficientMerge.Poly := [(17, -4), (98, -12), (107, -16), (116, -8), (125, -4), (134, 4), (143, 6), (152, 10), (161, 18)]
theorem atom0155Coded_decode : atom0155 = SparsePolynomial.decodeCubic 9 atom0155Coded := by decide +kernel
theorem atom0155Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (15915 : Int) atom0155Coded) := by
  have h := atom0155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0156 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -14), ([1,1,4], -10), ([1,1,5], -6), ([1,1,6], 2), ([1,1,7], 10), ([1,1,8], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [1,1] 1 base02 := by decide +kernel
theorem eval_atom0156 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = (quadA (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10470 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156Coded : CoefficientMerge.Poly := [(10, -8), (91, -12), (92, -16), (93, -14), (94, -10), (95, -6), (96, 2), (97, 10), (98, 18)]
theorem atom0156Coded_decode : atom0156 = SparsePolynomial.decodeCubic 9 atom0156Coded := by decide +kernel
theorem atom0156Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (10470 : Int) atom0156Coded) := by
  have h := atom0156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0157 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -6), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -10), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -4), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -12), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -16), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -12), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -8), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -8), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -8), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -20), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -16), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -10), ([2,5,6], -14), ([2,5,7], -8), ([2,5,8], -8), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -12), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -20), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -12), ([3,5,6], -18), ([3,5,7], -8), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -8), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -10), ([4,5,6], -16), ([4,5,7], -8), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -4), ([5,5,6], -8), ([5,5,7], -4), ([5,5,8], 4), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 12), ([5,7,8], 16), ([5,8,8], 16), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem atom0157_data : atom0157 = SparsePolynomial.monoTimes [] 1 base03 := by decide +kernel
theorem eval_atom0157 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = (detB (outer g)) := by
  rw [atom0157_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67230 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (detB (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157Coded : CoefficientMerge.Poly := [(3, -2), (4, -2), (5, -2), (6, -2), (7, -2), (8, -2), (11, -2), (12, -6), (13, -4), (14, -4), (15, -4), (16, -4), (17, -4), (20, -2), (21, -8), (22, -6), (23, -6), (24, -4), (25, -4), (26, -4), (30, -6), (31, -10), (32, -10), (33, -8), (34, -4), (35, -4), (40, -4), (41, -8), (42, -8), (43, -4), (44, -4), (50, -4), (51, -8), (52, -4), (53, -4), (60, -4), (61, -4), (62, -4), (92, -2), (93, -4), (94, -2), (95, -4), (96, -4), (97, -4), (98, -4), (101, -4), (102, -12), (103, -8), (104, -12), (105, -10), (106, -8), (107, -8), (111, -8), (112, -12), (113, -16), (114, -14), (115, -8), (116, -8), (121, -4), (122, -12), (123, -12), (124, -8), (125, -8), (131, -8), (132, -12), (133, -8), (134, -8), (141, -4), (142, -4), (143, -4), (182, -2), (183, -8), (184, -6), (185, -8), (186, -6), (187, -4), (188, -6), (192, -10), (193, -16), (194, -20), (195, -16), (196, -8), (197, -12), (202, -6), (203, -16), (204, -14), (205, -8), (206, -8), (212, -10), (213, -14), (214, -8), (215, -8), (222, -4), (223, -4), (224, -4), (273, -4), (274, -10), (275, -12), (276, -10), (277, -4), (278, -6), (283, -8), (284, -20), (285, -18), (286, -8), (287, -8), (293, -12), (294, -18), (295, -8), (303, -6), (304, -4), (305, 4), (314, 8), (323, 8), (364, -2), (365, -8), (366, -8), (367, -4), (368, -4), (374, -10), (375, -16), (376, -8), (384, -6), (385, -4), (386, 4), (395, 8), (404, 8), (455, -4), (456, -8), (457, -4), (458, 4), (465, -6), (466, -4), (467, 12), (476, 16), (485, 16), (546, -2), (547, -2), (548, 6), (557, 16), (566, 16), (638, 8), (647, 16), (728, 8)]
theorem atom0157Coded_decode : atom0157 = SparsePolynomial.decodeCubic 9 atom0157Coded := by decide +kernel
theorem atom0157Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (67230 : Int) atom0157Coded) := by
  have h := atom0157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0158 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,8], 4), ([0,6,6], -1), ([0,6,8], 4), ([0,7,8], 4), ([0,8,8], 4)]
theorem atom0158_data : atom0158 = SparsePolynomial.monoTimes [0] 1 base04 := by decide +kernel
theorem eval_atom0158 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0158_data, SparsePolynomial.eval_monoTimes, eval_base04]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37440 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base04_nonneg g hg hA hB
  rw [eval_base04] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158Coded : CoefficientMerge.Poly := [(0, -1), (1, -2), (2, -2), (3, -2), (4, -2), (5, -2), (6, -2), (10, -1), (11, -2), (12, -2), (13, -2), (14, -2), (15, -2), (20, -1), (21, -2), (22, -2), (23, -2), (24, -2), (30, -1), (31, -2), (32, -2), (33, -2), (40, -1), (41, -2), (42, -2), (50, -1), (51, -2), (53, 4), (60, -1), (62, 4), (71, 4), (80, 4)]
theorem atom0158Coded_decode : atom0158 = SparsePolynomial.decodeCubic 9 atom0158Coded := by decide +kernel
theorem atom0158Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (37440 : Int) atom0158Coded) := by
  have h := atom0158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0159 : SparsePolynomial.Poly := [([0,0,8], -2), ([0,1,8], -2), ([0,2,8], -2), ([0,3,8], -2), ([0,4,8], -2), ([0,7,8], 2), ([0,8,8], 4)]
theorem atom0159_data : atom0159 = SparsePolynomial.monoTimes [0,8] 1 base05 := by decide +kernel
theorem eval_atom0159 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = (quadB (outer g) ![1,1,0] * g 0 * g 8) := by
  rw [atom0159_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40320 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159Coded : CoefficientMerge.Poly := [(8, -2), (17, -2), (26, -2), (35, -2), (44, -2), (71, 2), (80, 4)]
theorem atom0159Coded_decode : atom0159 = SparsePolynomial.decodeCubic 9 atom0159Coded := by decide +kernel
theorem atom0159Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (40320 : Int) atom0159Coded) := by
  have h := atom0159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block001 : CoefficientMerge.Poly := [(0, -37440), (1, -74880), (2, -74880), (3, -308160), (4, -308160), (5, -308160), (6, -308160), (7, -233280), (8, -313920), (10, -121200), (11, -308160), (12, -774720), (13, -567740), (14, -541440), (15, -541440), (16, -498580), (17, -610860), (20, -270720), (21, -1008000), (22, -774720), (23, -675900), (24, -541440), (25, -466560), (26, -547200), (30, -737280), (31, -1241280), (32, -1142460), (33, -1008000), (34, -466560), (35, -547200), (40, -504000), (41, -1008000), (42, -1008000), (43, -466560), (44, -547200), (50, -504000), (51, -1008000), (52, -466560), (53, -316800), (60, -504000), (61, -466560), (62, -316800), (71, 230400), (80, 311040), (91, -125640), (92, -400800), (93, -613140), (94, -416880), (95, -430560), (96, -445620), (97, -457920), (98, -469080), (101, -466560), (102, -1399680), (103, -1038320), (104, -1103220), (105, -1166400), (106, -1061200), (107, -1187760), (111, -933120), (112, -1452280), (113, -1569780), (114, -1632960), (115, -997160), (116, -1060440), (121, -492860), (122, -1175740), (123, -1360230), (124, -899390), (125, -878430), (131, -735480), (132, -1202040), (133, -703460), (134, -671820), (141, -466560), (142, -418530), (143, -371070), (151, 80050), (152, 303240), (161, 286470), (182, -233280), (183, -933120), (184, -699840), (185, -735480), (186, -699840), (187, -466560), (188, -699840), (192, -1166400), (193, -1866240), (194, -1937520), (195, -1866240), (196, -636120), (197, -477360), (202, -437472), (203, -876960), (204, -587520), (205, -298080), (206, -8640), (212, -369360), (213, -339120), (214, 39960), (215, 460080), (222, -45360), (223, 388260), (224, 928800), (232, 347760), (233, 1351350), (242, 933120), (273, -305280), (274, -796320), (275, -676800), (276, -557280), (277, -437760), (278, -318240), (283, -650088), (284, -1169280), (285, -783360), (286, -397440), (287, -11520), (293, -492480), (294, -452160), (295, 80640), (296, 613440), (303, -60480), (304, 558720), (305, 1238400), (313, 518400), (314, 1863360), (323, 1244160), (364, -232920), (365, -712584), (366, -507816), (367, -339480), (368, -171144), (374, -615600), (375, -565200), (376, 100800), (377, 766800), (384, -75600), (385, 698400), (386, 1548000), (394, 648000), (395, 2329200), (404, 1555200), (455, -246240), (456, -339120), (457, 60480), (458, 460080), (465, -90720), (466, 838080), (467, 1857600), (475, 777600), (476, 2795040), (485, 1866240), (546, -35280), (547, 488880), (548, 1083600), (556, 907200), (557, 3260880), (566, 2177280), (637, 345600), (638, 1863360), (647, 2488320), (728, 933120)]
theorem block001_data : block001 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (297000 : Int) atom0080Coded) (CoefficientMerge.scale (922320 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (262368 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (692820 : Int) atom0083Coded) (CoefficientMerge.scale (1045440 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (635040 : Int) atom0085Coded) (CoefficientMerge.scale (924480 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (500580 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (997380 : Int) atom0088Coded) (CoefficientMerge.scale (775440 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1195560 : Int) atom0090Coded) (CoefficientMerge.scale (421200 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854820 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1395360 : Int) atom0093Coded) (CoefficientMerge.scale (347760 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1351350 : Int) atom0095Coded) (CoefficientMerge.scale (933120 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161280 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370080 : Int) atom0098Coded) (CoefficientMerge.scale (525240 : Int) atom0099Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (609120 : Int) atom0100Coded) (CoefficientMerge.scale (28800 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (381600 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283032 : Int) atom0103Coded) (CoefficientMerge.scale (867060 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1316160 : Int) atom0105Coded) (CoefficientMerge.scale (535680 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (921600 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (610740 : Int) atom0108Coded) (CoefficientMerge.scale (1350900 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (816120 : Int) atom0110Coded) (CoefficientMerge.scale (811080 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (639360 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1025280 : Int) atom0113Coded) (CoefficientMerge.scale (771840 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (518400 : Int) atom0115Coded) (CoefficientMerge.scale (930240 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311040 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360 : Int) atom0118Coded) (CoefficientMerge.scale (121716 : Int) atom0119Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (425304 : Int) atom0120Coded) (CoefficientMerge.scale (127080 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (295416 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (353160 : Int) atom0123Coded) (CoefficientMerge.scale (1103400 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (836280 : Int) atom0125Coded) (CoefficientMerge.scale (964440 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (624240 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1164960 : Int) atom0128Coded) (CoefficientMerge.scale (1081440 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (648000 : Int) atom0130Coded) (CoefficientMerge.scale (1396080 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (622080 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121500 : Int) atom0133Coded) (CoefficientMerge.scale (495180 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (428220 : Int) atom0135Coded) (CoefficientMerge.scale (289980 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (609120 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1304640 : Int) atom0138Coded) (CoefficientMerge.scale (853200 : Int) atom0139Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (777600 : Int) atom0140Coded) (CoefficientMerge.scale (1324080 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (395280 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (198000 : Int) atom0143Coded) (CoefficientMerge.scale (722160 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (383760 : Int) atom0145Coded) (CoefficientMerge.scale (907200 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1394640 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (311040 : Int) atom0148Coded) (CoefficientMerge.scale (345600 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (930240 : Int) atom0150Coded) (CoefficientMerge.scale (622080 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49410 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6575 : Int) atom0153Coded) (CoefficientMerge.scale (8005 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15915 : Int) atom0155Coded) (CoefficientMerge.scale (10470 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67230 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37440 : Int) atom0158Coded) (CoefficientMerge.scale (40320 : Int) atom0159Coded)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) block001 := by
  rw [block001_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0080Coded_nonneg g hg hA hB) (atom0081Coded_nonneg g hg hA hB)) (add_nonneg (atom0082Coded_nonneg g hg hA hB) (add_nonneg (atom0083Coded_nonneg g hg hA hB) (atom0084Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0085Coded_nonneg g hg hA hB) (atom0086Coded_nonneg g hg hA hB)) (add_nonneg (atom0087Coded_nonneg g hg hA hB) (add_nonneg (atom0088Coded_nonneg g hg hA hB) (atom0089Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0090Coded_nonneg g hg hA hB) (atom0091Coded_nonneg g hg hA hB)) (add_nonneg (atom0092Coded_nonneg g hg hA hB) (add_nonneg (atom0093Coded_nonneg g hg hA hB) (atom0094Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0095Coded_nonneg g hg hA hB) (atom0096Coded_nonneg g hg hA hB)) (add_nonneg (atom0097Coded_nonneg g hg hA hB) (add_nonneg (atom0098Coded_nonneg g hg hA hB) (atom0099Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0100Coded_nonneg g hg hA hB) (atom0101Coded_nonneg g hg hA hB)) (add_nonneg (atom0102Coded_nonneg g hg hA hB) (add_nonneg (atom0103Coded_nonneg g hg hA hB) (atom0104Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0105Coded_nonneg g hg hA hB) (atom0106Coded_nonneg g hg hA hB)) (add_nonneg (atom0107Coded_nonneg g hg hA hB) (add_nonneg (atom0108Coded_nonneg g hg hA hB) (atom0109Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0110Coded_nonneg g hg hA hB) (atom0111Coded_nonneg g hg hA hB)) (add_nonneg (atom0112Coded_nonneg g hg hA hB) (add_nonneg (atom0113Coded_nonneg g hg hA hB) (atom0114Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0115Coded_nonneg g hg hA hB) (atom0116Coded_nonneg g hg hA hB)) (add_nonneg (atom0117Coded_nonneg g hg hA hB) (add_nonneg (atom0118Coded_nonneg g hg hA hB) (atom0119Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0120Coded_nonneg g hg hA hB) (atom0121Coded_nonneg g hg hA hB)) (add_nonneg (atom0122Coded_nonneg g hg hA hB) (add_nonneg (atom0123Coded_nonneg g hg hA hB) (atom0124Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0125Coded_nonneg g hg hA hB) (atom0126Coded_nonneg g hg hA hB)) (add_nonneg (atom0127Coded_nonneg g hg hA hB) (add_nonneg (atom0128Coded_nonneg g hg hA hB) (atom0129Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0130Coded_nonneg g hg hA hB) (atom0131Coded_nonneg g hg hA hB)) (add_nonneg (atom0132Coded_nonneg g hg hA hB) (add_nonneg (atom0133Coded_nonneg g hg hA hB) (atom0134Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0135Coded_nonneg g hg hA hB) (atom0136Coded_nonneg g hg hA hB)) (add_nonneg (atom0137Coded_nonneg g hg hA hB) (add_nonneg (atom0138Coded_nonneg g hg hA hB) (atom0139Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0140Coded_nonneg g hg hA hB) (atom0141Coded_nonneg g hg hA hB)) (add_nonneg (atom0142Coded_nonneg g hg hA hB) (add_nonneg (atom0143Coded_nonneg g hg hA hB) (atom0144Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0145Coded_nonneg g hg hA hB) (atom0146Coded_nonneg g hg hA hB)) (add_nonneg (atom0147Coded_nonneg g hg hA hB) (add_nonneg (atom0148Coded_nonneg g hg hA hB) (atom0149Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0150Coded_nonneg g hg hA hB) (atom0151Coded_nonneg g hg hA hB)) (add_nonneg (atom0152Coded_nonneg g hg hA hB) (add_nonneg (atom0153Coded_nonneg g hg hA hB) (atom0154Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0155Coded_nonneg g hg hA hB) (atom0156Coded_nonneg g hg hA hB)) (add_nonneg (atom0157Coded_nonneg g hg hA hB) (add_nonneg (atom0158Coded_nonneg g hg hA hB) (atom0159Coded_nonneg g hg hA hB))))))))

end APPT.Finite9
