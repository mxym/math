import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0849 : SparsePolynomial.Poly := [([2,5,13], 1)]
theorem eval_atom0849 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0849 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0849, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0849_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250762389292800 : Int) atom0849) := by
  rw [SparsePolynomial.eval_scale, eval_atom0849]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0849Coded : CoefficientMerge.Poly := [(1285, 1)]
theorem atom0849Coded_decode : atom0849 = SparsePolynomial.decodeCubic 24 atom0849Coded := by decide +kernel
theorem atom0849Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) := by
  have h := atom0849_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0849Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0850 : SparsePolynomial.Poly := [([2,5,14], 1)]
theorem eval_atom0850 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0850 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0850, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0850_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (222902250278400 : Int) atom0850) := by
  rw [SparsePolynomial.eval_scale, eval_atom0850]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0850Coded : CoefficientMerge.Poly := [(1286, 1)]
theorem atom0850Coded_decode : atom0850 = SparsePolynomial.decodeCubic 24 atom0850Coded := by decide +kernel
theorem atom0850Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded) := by
  have h := atom0850_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0850Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0851 : SparsePolynomial.Poly := [([2,5,15], 1)]
theorem eval_atom0851 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0851 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0851, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0851_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225353863526400 : Int) atom0851) := by
  rw [SparsePolynomial.eval_scale, eval_atom0851]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0851Coded : CoefficientMerge.Poly := [(1287, 1)]
theorem atom0851Coded_decode : atom0851 = SparsePolynomial.decodeCubic 24 atom0851Coded := by decide +kernel
theorem atom0851Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) := by
  have h := atom0851_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0851Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0852 : SparsePolynomial.Poly := [([2,5,16], 1)]
theorem eval_atom0852 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0852 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0852, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0852_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215982966528000 : Int) atom0852) := by
  rw [SparsePolynomial.eval_scale, eval_atom0852]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0852Coded : CoefficientMerge.Poly := [(1288, 1)]
theorem atom0852Coded_decode : atom0852 = SparsePolynomial.decodeCubic 24 atom0852Coded := by decide +kernel
theorem atom0852Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) := by
  have h := atom0852_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0852Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0853 : SparsePolynomial.Poly := [([2,5,17], 1)]
theorem eval_atom0853 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0853 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0853, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0853_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216544807987200 : Int) atom0853) := by
  rw [SparsePolynomial.eval_scale, eval_atom0853]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0853Coded : CoefficientMerge.Poly := [(1289, 1)]
theorem atom0853Coded_decode : atom0853 = SparsePolynomial.decodeCubic 24 atom0853Coded := by decide +kernel
theorem atom0853Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded) := by
  have h := atom0853_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0853Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0854 : SparsePolynomial.Poly := [([2,5,18], 1)]
theorem eval_atom0854 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0854 = ((g 2) * (g 5) * (g 18)) := by
  norm_num [atom0854, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0854_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257815027008000 : Int) atom0854) := by
  rw [SparsePolynomial.eval_scale, eval_atom0854]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0854Coded : CoefficientMerge.Poly := [(1290, 1)]
theorem atom0854Coded_decode : atom0854 = SparsePolynomial.decodeCubic 24 atom0854Coded := by decide +kernel
theorem atom0854Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) := by
  have h := atom0854_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0854Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0855 : SparsePolynomial.Poly := [([2,5,19], 1)]
theorem eval_atom0855 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0855 = ((g 2) * (g 5) * (g 19)) := by
  norm_num [atom0855, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0855_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189421289164800 : Int) atom0855) := by
  rw [SparsePolynomial.eval_scale, eval_atom0855]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0855Coded : CoefficientMerge.Poly := [(1291, 1)]
theorem atom0855Coded_decode : atom0855 = SparsePolynomial.decodeCubic 24 atom0855Coded := by decide +kernel
theorem atom0855Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded) := by
  have h := atom0855_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0855Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0856 : SparsePolynomial.Poly := [([2,5,20], 1)]
theorem eval_atom0856 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0856 = ((g 2) * (g 5) * (g 20)) := by
  norm_num [atom0856, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0856_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (268578751795200 : Int) atom0856) := by
  rw [SparsePolynomial.eval_scale, eval_atom0856]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0856Coded : CoefficientMerge.Poly := [(1292, 1)]
theorem atom0856Coded_decode : atom0856 = SparsePolynomial.decodeCubic 24 atom0856Coded := by decide +kernel
theorem atom0856Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) := by
  have h := atom0856_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0856Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0857 : SparsePolynomial.Poly := [([2,5,21], 1)]
theorem eval_atom0857 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0857 = ((g 2) * (g 5) * (g 21)) := by
  norm_num [atom0857, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0857_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215630979379200 : Int) atom0857) := by
  rw [SparsePolynomial.eval_scale, eval_atom0857]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0857Coded : CoefficientMerge.Poly := [(1293, 1)]
theorem atom0857Coded_decode : atom0857 = SparsePolynomial.decodeCubic 24 atom0857Coded := by decide +kernel
theorem atom0857Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) := by
  have h := atom0857_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0857Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0858 : SparsePolynomial.Poly := [([2,5,22], 1)]
theorem eval_atom0858 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0858 = ((g 2) * (g 5) * (g 22)) := by
  norm_num [atom0858, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0858_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228830374080000 : Int) atom0858) := by
  rw [SparsePolynomial.eval_scale, eval_atom0858]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0858Coded : CoefficientMerge.Poly := [(1294, 1)]
theorem atom0858Coded_decode : atom0858 = SparsePolynomial.decodeCubic 24 atom0858Coded := by decide +kernel
theorem atom0858Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded) := by
  have h := atom0858_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0858Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0859 : SparsePolynomial.Poly := [([2,5,23], 1)]
theorem eval_atom0859 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0859 = ((g 2) * (g 5) * (g 23)) := by
  norm_num [atom0859, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0859_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274763154758400 : Int) atom0859) := by
  rw [SparsePolynomial.eval_scale, eval_atom0859]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0859Coded : CoefficientMerge.Poly := [(1295, 1)]
theorem atom0859Coded_decode : atom0859 = SparsePolynomial.decodeCubic 24 atom0859Coded := by decide +kernel
theorem atom0859Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) := by
  have h := atom0859_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0859Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0860 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0860 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0860 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0860, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0860_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126234564825600 : Int) atom0860) := by
  rw [SparsePolynomial.eval_scale, eval_atom0860]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0860Coded : CoefficientMerge.Poly := [(1302, 1)]
theorem atom0860Coded_decode : atom0860 = SparsePolynomial.decodeCubic 24 atom0860Coded := by decide +kernel
theorem atom0860Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded) := by
  have h := atom0860_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0860Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0861 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0861 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0861 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0861, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0861_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224731214400000 : Int) atom0861) := by
  rw [SparsePolynomial.eval_scale, eval_atom0861]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0861Coded : CoefficientMerge.Poly := [(1303, 1)]
theorem atom0861Coded_decode : atom0861 = SparsePolynomial.decodeCubic 24 atom0861Coded := by decide +kernel
theorem atom0861Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) := by
  have h := atom0861_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0861Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0862 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0862 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0862 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0862, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0862_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202842807552000 : Int) atom0862) := by
  rw [SparsePolynomial.eval_scale, eval_atom0862]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0862Coded : CoefficientMerge.Poly := [(1304, 1)]
theorem atom0862Coded_decode : atom0862 = SparsePolynomial.decodeCubic 24 atom0862Coded := by decide +kernel
theorem atom0862Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) := by
  have h := atom0862_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0862Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0863 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0863 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0863 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0863, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0863_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206600779625328 : Int) atom0863) := by
  rw [SparsePolynomial.eval_scale, eval_atom0863]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0863Coded : CoefficientMerge.Poly := [(1305, 1)]
theorem atom0863Coded_decode : atom0863 = SparsePolynomial.decodeCubic 24 atom0863Coded := by decide +kernel
theorem atom0863Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded) := by
  have h := atom0863_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0863Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0864 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0864 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0864 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0864, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0864_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226908137622672 : Int) atom0864) := by
  rw [SparsePolynomial.eval_scale, eval_atom0864]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0864Coded : CoefficientMerge.Poly := [(1306, 1)]
theorem atom0864Coded_decode : atom0864 = SparsePolynomial.decodeCubic 24 atom0864Coded := by decide +kernel
theorem atom0864Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) := by
  have h := atom0864_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0864Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0865 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0865 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0865 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0865, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0865_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237208830575904 : Int) atom0865) := by
  rw [SparsePolynomial.eval_scale, eval_atom0865]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0865Coded : CoefficientMerge.Poly := [(1307, 1)]
theorem atom0865Coded_decode : atom0865 = SparsePolynomial.decodeCubic 24 atom0865Coded := by decide +kernel
theorem atom0865Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded) := by
  have h := atom0865_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0865Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0866 : SparsePolynomial.Poly := [([2,6,12], 1)]
theorem eval_atom0866 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0866 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0866, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0866_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (263089627314624 : Int) atom0866) := by
  rw [SparsePolynomial.eval_scale, eval_atom0866]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0866Coded : CoefficientMerge.Poly := [(1308, 1)]
theorem atom0866Coded_decode : atom0866 = SparsePolynomial.decodeCubic 24 atom0866Coded := by decide +kernel
theorem atom0866Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) := by
  have h := atom0866_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0866Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0867 : SparsePolynomial.Poly := [([2,6,13], 1)]
theorem eval_atom0867 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0867 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0867, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0867_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254449759132800 : Int) atom0867) := by
  rw [SparsePolynomial.eval_scale, eval_atom0867]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0867Coded : CoefficientMerge.Poly := [(1309, 1)]
theorem atom0867Coded_decode : atom0867 = SparsePolynomial.decodeCubic 24 atom0867Coded := by decide +kernel
theorem atom0867Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) := by
  have h := atom0867_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0867Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0868 : SparsePolynomial.Poly := [([2,6,14], 1)]
theorem eval_atom0868 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0868 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0868, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0868_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242135628134400 : Int) atom0868) := by
  rw [SparsePolynomial.eval_scale, eval_atom0868]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0868Coded : CoefficientMerge.Poly := [(1310, 1)]
theorem atom0868Coded_decode : atom0868 = SparsePolynomial.decodeCubic 24 atom0868Coded := by decide +kernel
theorem atom0868Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded) := by
  have h := atom0868_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0868Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0869 : SparsePolynomial.Poly := [([2,6,15], 1)]
theorem eval_atom0869 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0869 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0869, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0869_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244608503731200 : Int) atom0869) := by
  rw [SparsePolynomial.eval_scale, eval_atom0869]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0869Coded : CoefficientMerge.Poly := [(1311, 1)]
theorem atom0869Coded_decode : atom0869 = SparsePolynomial.decodeCubic 24 atom0869Coded := by decide +kernel
theorem atom0869Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) := by
  have h := atom0869_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0869Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0870 : SparsePolynomial.Poly := [([2,6,16], 1)]
theorem eval_atom0870 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0870 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0870, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0870_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235258869081600 : Int) atom0870) := by
  rw [SparsePolynomial.eval_scale, eval_atom0870]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0870Coded : CoefficientMerge.Poly := [(1312, 1)]
theorem atom0870Coded_decode : atom0870 = SparsePolynomial.decodeCubic 24 atom0870Coded := by decide +kernel
theorem atom0870Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded) := by
  have h := atom0870_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0870Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0871 : SparsePolynomial.Poly := [([2,6,17], 1)]
theorem eval_atom0871 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0871 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0871, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0871_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235841972889600 : Int) atom0871) := by
  rw [SparsePolynomial.eval_scale, eval_atom0871]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0871Coded : CoefficientMerge.Poly := [(1313, 1)]
theorem atom0871Coded_decode : atom0871 = SparsePolynomial.decodeCubic 24 atom0871Coded := by decide +kernel
theorem atom0871Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) := by
  have h := atom0871_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0871Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0872 : SparsePolynomial.Poly := [([2,6,18], 1)]
theorem eval_atom0872 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0872 = ((g 2) * (g 6) * (g 18)) := by
  norm_num [atom0872, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0872_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274348086566400 : Int) atom0872) := by
  rw [SparsePolynomial.eval_scale, eval_atom0872]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0872Coded : CoefficientMerge.Poly := [(1314, 1)]
theorem atom0872Coded_decode : atom0872 = SparsePolynomial.decodeCubic 24 atom0872Coded := by decide +kernel
theorem atom0872Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) := by
  have h := atom0872_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0872Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0873 : SparsePolynomial.Poly := [([2,6,19], 1)]
theorem eval_atom0873 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0873 = ((g 2) * (g 6) * (g 19)) := by
  norm_num [atom0873, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0873_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220533081753600 : Int) atom0873) := by
  rw [SparsePolynomial.eval_scale, eval_atom0873]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0873Coded : CoefficientMerge.Poly := [(1315, 1)]
theorem atom0873Coded_decode : atom0873 = SparsePolynomial.decodeCubic 24 atom0873Coded := by decide +kernel
theorem atom0873Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded) := by
  have h := atom0873_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0873Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0874 : SparsePolynomial.Poly := [([2,6,20], 1)]
theorem eval_atom0874 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0874 = ((g 2) * (g 6) * (g 20)) := by
  norm_num [atom0874, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0874_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (307559875392000 : Int) atom0874) := by
  rw [SparsePolynomial.eval_scale, eval_atom0874]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0874Coded : CoefficientMerge.Poly := [(1316, 1)]
theorem atom0874Coded_decode : atom0874 = SparsePolynomial.decodeCubic 24 atom0874Coded := by decide +kernel
theorem atom0874Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) := by
  have h := atom0874_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0874Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0875 : SparsePolynomial.Poly := [([2,6,21], 1)]
theorem eval_atom0875 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0875 = ((g 2) * (g 6) * (g 21)) := by
  norm_num [atom0875, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0875_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270329502643200 : Int) atom0875) := by
  rw [SparsePolynomial.eval_scale, eval_atom0875]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0875Coded : CoefficientMerge.Poly := [(1317, 1)]
theorem atom0875Coded_decode : atom0875 = SparsePolynomial.decodeCubic 24 atom0875Coded := by decide +kernel
theorem atom0875Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded) := by
  have h := atom0875_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0875Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0876 : SparsePolynomial.Poly := [([2,6,22], 1)]
theorem eval_atom0876 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0876 = ((g 2) * (g 6) * (g 22)) := by
  norm_num [atom0876, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0876_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299246297011200 : Int) atom0876) := by
  rw [SparsePolynomial.eval_scale, eval_atom0876]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0876Coded : CoefficientMerge.Poly := [(1318, 1)]
theorem atom0876Coded_decode : atom0876 = SparsePolynomial.decodeCubic 24 atom0876Coded := by decide +kernel
theorem atom0876Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) := by
  have h := atom0876_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0876Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0877 : SparsePolynomial.Poly := [([2,6,23], 1)]
theorem eval_atom0877 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0877 = ((g 2) * (g 6) * (g 23)) := by
  norm_num [atom0877, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0877_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360896477356800 : Int) atom0877) := by
  rw [SparsePolynomial.eval_scale, eval_atom0877]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0877Coded : CoefficientMerge.Poly := [(1319, 1)]
theorem atom0877Coded_decode : atom0877 = SparsePolynomial.decodeCubic 24 atom0877Coded := by decide +kernel
theorem atom0877Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) := by
  have h := atom0877_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0877Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0878 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0878 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0878 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0878, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0878_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135493136486400 : Int) atom0878) := by
  rw [SparsePolynomial.eval_scale, eval_atom0878]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0878Coded : CoefficientMerge.Poly := [(1327, 1)]
theorem atom0878Coded_decode : atom0878 = SparsePolynomial.decodeCubic 24 atom0878Coded := by decide +kernel
theorem atom0878Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded) := by
  have h := atom0878_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0878Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0879 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0879 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0879 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0879, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0879_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254285879232000 : Int) atom0879) := by
  rw [SparsePolynomial.eval_scale, eval_atom0879]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0879Coded : CoefficientMerge.Poly := [(1328, 1)]
theorem atom0879Coded_decode : atom0879 = SparsePolynomial.decodeCubic 24 atom0879Coded := by decide +kernel
theorem atom0879Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) := by
  have h := atom0879_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0879Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0880 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0880 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0880 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0880, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0880_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (240589825423728 : Int) atom0880) := by
  rw [SparsePolynomial.eval_scale, eval_atom0880]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0880Coded : CoefficientMerge.Poly := [(1329, 1)]
theorem atom0880Coded_decode : atom0880 = SparsePolynomial.decodeCubic 24 atom0880Coded := by decide +kernel
theorem atom0880Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded) := by
  have h := atom0880_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0880Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0881 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0881 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0881 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0881, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0881_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257835405193872 : Int) atom0881) := by
  rw [SparsePolynomial.eval_scale, eval_atom0881]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0881Coded : CoefficientMerge.Poly := [(1330, 1)]
theorem atom0881Coded_decode : atom0881 = SparsePolynomial.decodeCubic 24 atom0881Coded := by decide +kernel
theorem atom0881Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) := by
  have h := atom0881_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0881Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0882 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0882 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0882 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0882, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0882_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269199215587104 : Int) atom0882) := by
  rw [SparsePolynomial.eval_scale, eval_atom0882]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0882Coded : CoefficientMerge.Poly := [(1331, 1)]
theorem atom0882Coded_decode : atom0882 = SparsePolynomial.decodeCubic 24 atom0882Coded := by decide +kernel
theorem atom0882Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) := by
  have h := atom0882_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0882Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0883 : SparsePolynomial.Poly := [([2,7,12], 1)]
theorem eval_atom0883 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0883 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0883, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0883_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296143129765824 : Int) atom0883) := by
  rw [SparsePolynomial.eval_scale, eval_atom0883]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0883Coded : CoefficientMerge.Poly := [(1332, 1)]
theorem atom0883Coded_decode : atom0883 = SparsePolynomial.decodeCubic 24 atom0883Coded := by decide +kernel
theorem atom0883Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded) := by
  have h := atom0883_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0883Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0884 : SparsePolynomial.Poly := [([2,7,13], 1)]
theorem eval_atom0884 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0884 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0884, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0884_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (286503931190400 : Int) atom0884) := by
  rw [SparsePolynomial.eval_scale, eval_atom0884]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0884Coded : CoefficientMerge.Poly := [(1333, 1)]
theorem atom0884Coded_decode : atom0884 = SparsePolynomial.decodeCubic 24 atom0884Coded := by decide +kernel
theorem atom0884Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) := by
  have h := atom0884_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0884Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0885 : SparsePolynomial.Poly := [([2,7,14], 1)]
theorem eval_atom0885 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0885 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0885, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0885_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273190469798400 : Int) atom0885) := by
  rw [SparsePolynomial.eval_scale, eval_atom0885]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0885Coded : CoefficientMerge.Poly := [(1334, 1)]
theorem atom0885Coded_decode : atom0885 = SparsePolynomial.decodeCubic 24 atom0885Coded := by decide +kernel
theorem atom0885Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded) := by
  have h := atom0885_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0885Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0886 : SparsePolynomial.Poly := [([2,7,15], 1)]
theorem eval_atom0886 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0886 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0886, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0886_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274664015001600 : Int) atom0886) := by
  rw [SparsePolynomial.eval_scale, eval_atom0886]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0886Coded : CoefficientMerge.Poly := [(1335, 1)]
theorem atom0886Coded_decode : atom0886 = SparsePolynomial.decodeCubic 24 atom0886Coded := by decide +kernel
theorem atom0886Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) := by
  have h := atom0886_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0886Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0887 : SparsePolynomial.Poly := [([2,7,16], 1)]
theorem eval_atom0887 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0887 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0887, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0887_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264315049958400 : Int) atom0887) := by
  rw [SparsePolynomial.eval_scale, eval_atom0887]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0887Coded : CoefficientMerge.Poly := [(1336, 1)]
theorem atom0887Coded_decode : atom0887 = SparsePolynomial.decodeCubic 24 atom0887Coded := by decide +kernel
theorem atom0887Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) := by
  have h := atom0887_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0887Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0888 : SparsePolynomial.Poly := [([2,7,17], 1)]
theorem eval_atom0888 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0888 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0888, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0888_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (263898823372800 : Int) atom0888) := by
  rw [SparsePolynomial.eval_scale, eval_atom0888]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0888Coded : CoefficientMerge.Poly := [(1337, 1)]
theorem atom0888Coded_decode : atom0888 = SparsePolynomial.decodeCubic 24 atom0888Coded := by decide +kernel
theorem atom0888Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded) := by
  have h := atom0888_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0888Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0889 : SparsePolynomial.Poly := [([2,7,18], 1)]
theorem eval_atom0889 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0889 = ((g 2) * (g 7) * (g 18)) := by
  norm_num [atom0889, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0889_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (303735015091200 : Int) atom0889) := by
  rw [SparsePolynomial.eval_scale, eval_atom0889]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0889Coded : CoefficientMerge.Poly := [(1338, 1)]
theorem atom0889Coded_decode : atom0889 = SparsePolynomial.decodeCubic 24 atom0889Coded := by decide +kernel
theorem atom0889Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) := by
  have h := atom0889_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0889Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0890 : SparsePolynomial.Poly := [([2,7,19], 1)]
theorem eval_atom0890 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0890 = ((g 2) * (g 7) * (g 19)) := by
  norm_num [atom0890, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0890_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253579496755200 : Int) atom0890) := by
  rw [SparsePolynomial.eval_scale, eval_atom0890]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0890Coded : CoefficientMerge.Poly := [(1339, 1)]
theorem atom0890Coded_decode : atom0890 = SparsePolynomial.decodeCubic 24 atom0890Coded := by decide +kernel
theorem atom0890Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded) := by
  have h := atom0890_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0890Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0891 : SparsePolynomial.Poly := [([2,7,20], 1)]
theorem eval_atom0891 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0891 = ((g 2) * (g 7) * (g 20)) := by
  norm_num [atom0891, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0891_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344265776870400 : Int) atom0891) := by
  rw [SparsePolynomial.eval_scale, eval_atom0891]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0891Coded : CoefficientMerge.Poly := [(1340, 1)]
theorem atom0891Coded_decode : atom0891 = SparsePolynomial.decodeCubic 24 atom0891Coded := by decide +kernel
theorem atom0891Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) := by
  have h := atom0891_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0891Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0892 : SparsePolynomial.Poly := [([2,7,21], 1)]
theorem eval_atom0892 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0892 = ((g 2) * (g 7) * (g 21)) := by
  norm_num [atom0892, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0892_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (315353707468800 : Int) atom0892) := by
  rw [SparsePolynomial.eval_scale, eval_atom0892]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0892Coded : CoefficientMerge.Poly := [(1341, 1)]
theorem atom0892Coded_decode : atom0892 = SparsePolynomial.decodeCubic 24 atom0892Coded := by decide +kernel
theorem atom0892Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) := by
  have h := atom0892_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0892Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0893 : SparsePolynomial.Poly := [([2,7,22], 1)]
theorem eval_atom0893 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0893 = ((g 2) * (g 7) * (g 22)) := by
  norm_num [atom0893, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0893_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352588805184000 : Int) atom0893) := by
  rw [SparsePolynomial.eval_scale, eval_atom0893]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0893Coded : CoefficientMerge.Poly := [(1342, 1)]
theorem atom0893Coded_decode : atom0893 = SparsePolynomial.decodeCubic 24 atom0893Coded := by decide +kernel
theorem atom0893Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded) := by
  have h := atom0893_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0893Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0894 : SparsePolynomial.Poly := [([2,7,23], 1)]
theorem eval_atom0894 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0894 = ((g 2) * (g 7) * (g 23)) := by
  norm_num [atom0894, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0894_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422557288876800 : Int) atom0894) := by
  rw [SparsePolynomial.eval_scale, eval_atom0894]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0894Coded : CoefficientMerge.Poly := [(1343, 1)]
theorem atom0894Coded_decode : atom0894 = SparsePolynomial.decodeCubic 24 atom0894Coded := by decide +kernel
theorem atom0894Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) := by
  have h := atom0894_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0894Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0895 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0895 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156809822400000 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895Coded : CoefficientMerge.Poly := [(1352, 1)]
theorem atom0895Coded_decode : atom0895 = SparsePolynomial.decodeCubic 24 atom0895Coded := by decide +kernel
theorem atom0895Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded) := by
  have h := atom0895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0896 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0896 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298917689941728 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896Coded : CoefficientMerge.Poly := [(1353, 1)]
theorem atom0896Coded_decode : atom0896 = SparsePolynomial.decodeCubic 24 atom0896Coded := by decide +kernel
theorem atom0896Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) := by
  have h := atom0896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0897 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0897 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (285877758467664 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897Coded : CoefficientMerge.Poly := [(1354, 1)]
theorem atom0897Coded_decode : atom0897 = SparsePolynomial.decodeCubic 24 atom0897Coded := by decide +kernel
theorem atom0897Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) := by
  have h := atom0897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0898 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0898 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299464987862304 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898Coded : CoefficientMerge.Poly := [(1355, 1)]
theorem atom0898Coded_decode : atom0898 = SparsePolynomial.decodeCubic 24 atom0898Coded := by decide +kernel
theorem atom0898Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded) := by
  have h := atom0898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0899 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0899 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321305938329024 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899Coded : CoefficientMerge.Poly := [(1356, 1)]
theorem atom0899Coded_decode : atom0899 = SparsePolynomial.decodeCubic 24 atom0899Coded := by decide +kernel
theorem atom0899Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) := by
  have h := atom0899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0900 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0900 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309646816617600 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900Coded : CoefficientMerge.Poly := [(1357, 1)]
theorem atom0900Coded_decode : atom0900 = SparsePolynomial.decodeCubic 24 atom0900Coded := by decide +kernel
theorem atom0900Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded) := by
  have h := atom0900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0901 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0901 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (294313432089600 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901Coded : CoefficientMerge.Poly := [(1358, 1)]
theorem atom0901Coded_decode : atom0901 = SparsePolynomial.decodeCubic 24 atom0901Coded := by decide +kernel
theorem atom0901Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) := by
  have h := atom0901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0902 : SparsePolynomial.Poly := [([2,8,15], 1)]
theorem eval_atom0902 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (293767054156800 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902Coded : CoefficientMerge.Poly := [(1359, 1)]
theorem atom0902Coded_decode : atom0902 = SparsePolynomial.decodeCubic 24 atom0902Coded := by decide +kernel
theorem atom0902Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) := by
  have h := atom0902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0903 : SparsePolynomial.Poly := [([2,8,16], 1)]
theorem eval_atom0903 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (281398165977600 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903Coded : CoefficientMerge.Poly := [(1360, 1)]
theorem atom0903Coded_decode : atom0903 = SparsePolynomial.decodeCubic 24 atom0903Coded := by decide +kernel
theorem atom0903Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded) := by
  have h := atom0903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0904 : SparsePolynomial.Poly := [([2,8,17], 1)]
theorem eval_atom0904 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278962016256000 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904Coded : CoefficientMerge.Poly := [(1361, 1)]
theorem atom0904Coded_decode : atom0904 = SparsePolynomial.decodeCubic 24 atom0904Coded := by decide +kernel
theorem atom0904Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) := by
  have h := atom0904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0905 : SparsePolynomial.Poly := [([2,8,18], 1)]
theorem eval_atom0905 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 2) * (g 8) * (g 18)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320232235276800 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905Coded : CoefficientMerge.Poly := [(1362, 1)]
theorem atom0905Coded_decode : atom0905 = SparsePolynomial.decodeCubic 24 atom0905Coded := by decide +kernel
theorem atom0905Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded) := by
  have h := atom0905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0906 : SparsePolynomial.Poly := [([2,8,19], 1)]
theorem eval_atom0906 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 2) * (g 8) * (g 19)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (274964694681600 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906Coded : CoefficientMerge.Poly := [(1363, 1)]
theorem atom0906Coded_decode : atom0906 = SparsePolynomial.decodeCubic 24 atom0906Coded := by decide +kernel
theorem atom0906Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) := by
  have h := atom0906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0907 : SparsePolynomial.Poly := [([2,8,20], 1)]
theorem eval_atom0907 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 2) * (g 8) * (g 20)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370538952537600 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907Coded : CoefficientMerge.Poly := [(1364, 1)]
theorem atom0907Coded_decode : atom0907 = SparsePolynomial.decodeCubic 24 atom0907Coded := by decide +kernel
theorem atom0907Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) := by
  have h := atom0907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0908 : SparsePolynomial.Poly := [([2,8,21], 1)]
theorem eval_atom0908 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 2) * (g 8) * (g 21)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353422761753600 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908Coded : CoefficientMerge.Poly := [(1365, 1)]
theorem atom0908Coded_decode : atom0908 = SparsePolynomial.decodeCubic 24 atom0908Coded := by decide +kernel
theorem atom0908Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded) := by
  have h := atom0908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0909 : SparsePolynomial.Poly := [([2,8,22], 1)]
theorem eval_atom0909 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 2) * (g 8) * (g 22)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402453738086400 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909Coded : CoefficientMerge.Poly := [(1366, 1)]
theorem atom0909Coded_decode : atom0909 = SparsePolynomial.decodeCubic 24 atom0909Coded := by decide +kernel
theorem atom0909Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) := by
  have h := atom0909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0910 : SparsePolynomial.Poly := [([2,8,23], 1)]
theorem eval_atom0910 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 2) * (g 8) * (g 23)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484218100396800 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910Coded : CoefficientMerge.Poly := [(1367, 1)]
theorem atom0910Coded_decode : atom0910 = SparsePolynomial.decodeCubic 24 atom0910Coded := by decide +kernel
theorem atom0910Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded) := by
  have h := atom0910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0911 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0911 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183207987772128 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911Coded : CoefficientMerge.Poly := [(1377, 1)]
theorem atom0911Coded_decode : atom0911 = SparsePolynomial.decodeCubic 24 atom0911Coded := by decide +kernel
theorem atom0911Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) := by
  have h := atom0911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0912 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0912 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350273600335296 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912Coded : CoefficientMerge.Poly := [(1378, 1)]
theorem atom0912Coded_decode : atom0912 = SparsePolynomial.decodeCubic 24 atom0912Coded := by decide +kernel
theorem atom0912Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) := by
  have h := atom0912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0913 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0913 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (338777815302432 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913Coded : CoefficientMerge.Poly := [(1379, 1)]
theorem atom0913Coded_decode : atom0913 = SparsePolynomial.decodeCubic 24 atom0913Coded := by decide +kernel
theorem atom0913Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded) := by
  have h := atom0913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0914 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0914 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360661290466752 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914Coded : CoefficientMerge.Poly := [(1380, 1)]
theorem atom0914Coded_decode : atom0914 = SparsePolynomial.decodeCubic 24 atom0914Coded := by decide +kernel
theorem atom0914Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) := by
  have h := atom0914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0915 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0915 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342878612300928 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915Coded : CoefficientMerge.Poly := [(1381, 1)]
theorem atom0915Coded_decode : atom0915 = SparsePolynomial.decodeCubic 24 atom0915Coded := by decide +kernel
theorem atom0915Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded) := by
  have h := atom0915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0916 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0916 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324504711894528 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916Coded : CoefficientMerge.Poly := [(1382, 1)]
theorem atom0916Coded_decode : atom0916 = SparsePolynomial.decodeCubic 24 atom0916Coded := by decide +kernel
theorem atom0916Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) := by
  have h := atom0916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0917 : SparsePolynomial.Poly := [([2,9,15], 1)]
theorem eval_atom0917 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320917818083328 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917Coded : CoefficientMerge.Poly := [(1383, 1)]
theorem atom0917Coded_decode : atom0917 = SparsePolynomial.decodeCubic 24 atom0917Coded := by decide +kernel
theorem atom0917Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) := by
  have h := atom0917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0918 : SparsePolynomial.Poly := [([2,9,16], 1)]
theorem eval_atom0918 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305508414025728 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918Coded : CoefficientMerge.Poly := [(1384, 1)]
theorem atom0918Coded_decode : atom0918 = SparsePolynomial.decodeCubic 24 atom0918Coded := by decide +kernel
theorem atom0918Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded) := by
  have h := atom0918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0919 : SparsePolynomial.Poly := [([2,9,17], 1)]
theorem eval_atom0919 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (300031748425728 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919Coded : CoefficientMerge.Poly := [(1385, 1)]
theorem atom0919Coded_decode : atom0919 = SparsePolynomial.decodeCubic 24 atom0919Coded := by decide +kernel
theorem atom0919Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) := by
  have h := atom0919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0920 : SparsePolynomial.Poly := [([2,9,18], 1)]
theorem eval_atom0920 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 2) * (g 9) * (g 18)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340464919398912 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920Coded : CoefficientMerge.Poly := [(1386, 1)]
theorem atom0920Coded_decode : atom0920 = SparsePolynomial.decodeCubic 24 atom0920Coded := by decide +kernel
theorem atom0920Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded) := by
  have h := atom0920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0921 : SparsePolynomial.Poly := [([2,9,19], 1)]
theorem eval_atom0921 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 2) * (g 9) * (g 19)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296563798586880 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921Coded : CoefficientMerge.Poly := [(1387, 1)]
theorem atom0921Coded_decode : atom0921 = SparsePolynomial.decodeCubic 24 atom0921Coded := by decide +kernel
theorem atom0921Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) := by
  have h := atom0921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0922 : SparsePolynomial.Poly := [([2,9,20], 1)]
theorem eval_atom0922 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 2) * (g 9) * (g 20)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393504476226048 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922Coded : CoefficientMerge.Poly := [(1388, 1)]
theorem atom0922Coded_decode : atom0922 = SparsePolynomial.decodeCubic 24 atom0922Coded := by decide +kernel
theorem atom0922Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) := by
  have h := atom0922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0923 : SparsePolynomial.Poly := [([2,9,21], 1)]
theorem eval_atom0923 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 2) * (g 9) * (g 21)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382161640886784 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923Coded : CoefficientMerge.Poly := [(1389, 1)]
theorem atom0923Coded_decode : atom0923 = SparsePolynomial.decodeCubic 24 atom0923Coded := by decide +kernel
theorem atom0923Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded) := by
  have h := atom0923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0924 : SparsePolynomial.Poly := [([2,9,22], 1)]
theorem eval_atom0924 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 2) * (g 9) * (g 22)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436965972664320 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924Coded : CoefficientMerge.Poly := [(1390, 1)]
theorem atom0924Coded_decode : atom0924 = SparsePolynomial.decodeCubic 24 atom0924Coded := by decide +kernel
theorem atom0924Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) := by
  have h := atom0924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0925 : SparsePolynomial.Poly := [([2,9,23], 1)]
theorem eval_atom0925 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 2) * (g 9) * (g 23)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524503690419456 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925Coded : CoefficientMerge.Poly := [(1391, 1)]
theorem atom0925Coded_decode : atom0925 = SparsePolynomial.decodeCubic 24 atom0925Coded := by decide +kernel
theorem atom0925Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded) := by
  have h := atom0925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0926 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0926 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208165732793568 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926Coded : CoefficientMerge.Poly := [(1402, 1)]
theorem atom0926Coded_decode : atom0926 = SparsePolynomial.decodeCubic 24 atom0926Coded := by decide +kernel
theorem atom0926Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) := by
  have h := atom0926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0927 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0927 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (407982508176672 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927Coded : CoefficientMerge.Poly := [(1403, 1)]
theorem atom0927Coded_decode : atom0927 = SparsePolynomial.decodeCubic 24 atom0927Coded := by decide +kernel
theorem atom0927Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) := by
  have h := atom0927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0928 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0928 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422721834144192 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928Coded : CoefficientMerge.Poly := [(1404, 1)]
theorem atom0928Coded_decode : atom0928 = SparsePolynomial.decodeCubic 24 atom0928Coded := by decide +kernel
theorem atom0928Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded) := by
  have h := atom0928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block013 : CoefficientMerge.Poly := [(1285, 250762389292800), (1286, 222902250278400), (1287, 225353863526400), (1288, 215982966528000), (1289, 216544807987200), (1290, 257815027008000), (1291, 189421289164800), (1292, 268578751795200), (1293, 215630979379200), (1294, 228830374080000), (1295, 274763154758400), (1302, 126234564825600), (1303, 224731214400000), (1304, 202842807552000), (1305, 206600779625328), (1306, 226908137622672), (1307, 237208830575904), (1308, 263089627314624), (1309, 254449759132800), (1310, 242135628134400), (1311, 244608503731200), (1312, 235258869081600), (1313, 235841972889600), (1314, 274348086566400), (1315, 220533081753600), (1316, 307559875392000), (1317, 270329502643200), (1318, 299246297011200), (1319, 360896477356800), (1327, 135493136486400), (1328, 254285879232000), (1329, 240589825423728), (1330, 257835405193872), (1331, 269199215587104), (1332, 296143129765824), (1333, 286503931190400), (1334, 273190469798400), (1335, 274664015001600), (1336, 264315049958400), (1337, 263898823372800), (1338, 303735015091200), (1339, 253579496755200), (1340, 344265776870400), (1341, 315353707468800), (1342, 352588805184000), (1343, 422557288876800), (1352, 156809822400000), (1353, 298917689941728), (1354, 285877758467664), (1355, 299464987862304), (1356, 321305938329024), (1357, 309646816617600), (1358, 294313432089600), (1359, 293767054156800), (1360, 281398165977600), (1361, 278962016256000), (1362, 320232235276800), (1363, 274964694681600), (1364, 370538952537600), (1365, 353422761753600), (1366, 402453738086400), (1367, 484218100396800), (1377, 183207987772128), (1378, 350273600335296), (1379, 338777815302432), (1380, 360661290466752), (1381, 342878612300928), (1382, 324504711894528), (1383, 320917818083328), (1384, 305508414025728), (1385, 300031748425728), (1386, 340464919398912), (1387, 296563798586880), (1388, 393504476226048), (1389, 382161640886784), (1390, 436965972664320), (1391, 524503690419456), (1402, 208165732793568), (1403, 407982508176672), (1404, 422721834144192)]
theorem block013_data : block013 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250762389292800 : Int) atom0849Coded) (CoefficientMerge.scale (222902250278400 : Int) atom0850Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225353863526400 : Int) atom0851Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215982966528000 : Int) atom0852Coded) (CoefficientMerge.scale (216544807987200 : Int) atom0853Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (257815027008000 : Int) atom0854Coded) (CoefficientMerge.scale (189421289164800 : Int) atom0855Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (268578751795200 : Int) atom0856Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215630979379200 : Int) atom0857Coded) (CoefficientMerge.scale (228830374080000 : Int) atom0858Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (274763154758400 : Int) atom0859Coded) (CoefficientMerge.scale (126234564825600 : Int) atom0860Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224731214400000 : Int) atom0861Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202842807552000 : Int) atom0862Coded) (CoefficientMerge.scale (206600779625328 : Int) atom0863Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (226908137622672 : Int) atom0864Coded) (CoefficientMerge.scale (237208830575904 : Int) atom0865Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (263089627314624 : Int) atom0866Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254449759132800 : Int) atom0867Coded) (CoefficientMerge.scale (242135628134400 : Int) atom0868Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (244608503731200 : Int) atom0869Coded) (CoefficientMerge.scale (235258869081600 : Int) atom0870Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (235841972889600 : Int) atom0871Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274348086566400 : Int) atom0872Coded) (CoefficientMerge.scale (220533081753600 : Int) atom0873Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (307559875392000 : Int) atom0874Coded) (CoefficientMerge.scale (270329502643200 : Int) atom0875Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299246297011200 : Int) atom0876Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360896477356800 : Int) atom0877Coded) (CoefficientMerge.scale (135493136486400 : Int) atom0878Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254285879232000 : Int) atom0879Coded) (CoefficientMerge.scale (240589825423728 : Int) atom0880Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (257835405193872 : Int) atom0881Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269199215587104 : Int) atom0882Coded) (CoefficientMerge.scale (296143129765824 : Int) atom0883Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (286503931190400 : Int) atom0884Coded) (CoefficientMerge.scale (273190469798400 : Int) atom0885Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274664015001600 : Int) atom0886Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264315049958400 : Int) atom0887Coded) (CoefficientMerge.scale (263898823372800 : Int) atom0888Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (303735015091200 : Int) atom0889Coded) (CoefficientMerge.scale (253579496755200 : Int) atom0890Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344265776870400 : Int) atom0891Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (315353707468800 : Int) atom0892Coded) (CoefficientMerge.scale (352588805184000 : Int) atom0893Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (422557288876800 : Int) atom0894Coded) (CoefficientMerge.scale (156809822400000 : Int) atom0895Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298917689941728 : Int) atom0896Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (285877758467664 : Int) atom0897Coded) (CoefficientMerge.scale (299464987862304 : Int) atom0898Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (321305938329024 : Int) atom0899Coded) (CoefficientMerge.scale (309646816617600 : Int) atom0900Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (294313432089600 : Int) atom0901Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (293767054156800 : Int) atom0902Coded) (CoefficientMerge.scale (281398165977600 : Int) atom0903Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278962016256000 : Int) atom0904Coded) (CoefficientMerge.scale (320232235276800 : Int) atom0905Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (274964694681600 : Int) atom0906Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370538952537600 : Int) atom0907Coded) (CoefficientMerge.scale (353422761753600 : Int) atom0908Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (402453738086400 : Int) atom0909Coded) (CoefficientMerge.scale (484218100396800 : Int) atom0910Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183207987772128 : Int) atom0911Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350273600335296 : Int) atom0912Coded) (CoefficientMerge.scale (338777815302432 : Int) atom0913Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360661290466752 : Int) atom0914Coded) (CoefficientMerge.scale (342878612300928 : Int) atom0915Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324504711894528 : Int) atom0916Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (320917818083328 : Int) atom0917Coded) (CoefficientMerge.scale (305508414025728 : Int) atom0918Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (300031748425728 : Int) atom0919Coded) (CoefficientMerge.scale (340464919398912 : Int) atom0920Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (296563798586880 : Int) atom0921Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (393504476226048 : Int) atom0922Coded) (CoefficientMerge.scale (382161640886784 : Int) atom0923Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (436965972664320 : Int) atom0924Coded) (CoefficientMerge.scale (524503690419456 : Int) atom0925Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208165732793568 : Int) atom0926Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (407982508176672 : Int) atom0927Coded) (CoefficientMerge.scale (422721834144192 : Int) atom0928Coded)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block013 := by
  rw [block013_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0849Coded_nonneg g hg hA hB) (atom0850Coded_nonneg g hg hA hB)) (add_nonneg (atom0851Coded_nonneg g hg hA hB) (add_nonneg (atom0852Coded_nonneg g hg hA hB) (atom0853Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0854Coded_nonneg g hg hA hB) (atom0855Coded_nonneg g hg hA hB)) (add_nonneg (atom0856Coded_nonneg g hg hA hB) (add_nonneg (atom0857Coded_nonneg g hg hA hB) (atom0858Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0859Coded_nonneg g hg hA hB) (atom0860Coded_nonneg g hg hA hB)) (add_nonneg (atom0861Coded_nonneg g hg hA hB) (add_nonneg (atom0862Coded_nonneg g hg hA hB) (atom0863Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0864Coded_nonneg g hg hA hB) (atom0865Coded_nonneg g hg hA hB)) (add_nonneg (atom0866Coded_nonneg g hg hA hB) (add_nonneg (atom0867Coded_nonneg g hg hA hB) (atom0868Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0869Coded_nonneg g hg hA hB) (atom0870Coded_nonneg g hg hA hB)) (add_nonneg (atom0871Coded_nonneg g hg hA hB) (add_nonneg (atom0872Coded_nonneg g hg hA hB) (atom0873Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0874Coded_nonneg g hg hA hB) (atom0875Coded_nonneg g hg hA hB)) (add_nonneg (atom0876Coded_nonneg g hg hA hB) (add_nonneg (atom0877Coded_nonneg g hg hA hB) (atom0878Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0879Coded_nonneg g hg hA hB) (atom0880Coded_nonneg g hg hA hB)) (add_nonneg (atom0881Coded_nonneg g hg hA hB) (add_nonneg (atom0882Coded_nonneg g hg hA hB) (atom0883Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0884Coded_nonneg g hg hA hB) (atom0885Coded_nonneg g hg hA hB)) (add_nonneg (atom0886Coded_nonneg g hg hA hB) (add_nonneg (atom0887Coded_nonneg g hg hA hB) (atom0888Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0889Coded_nonneg g hg hA hB) (atom0890Coded_nonneg g hg hA hB)) (add_nonneg (atom0891Coded_nonneg g hg hA hB) (add_nonneg (atom0892Coded_nonneg g hg hA hB) (atom0893Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0894Coded_nonneg g hg hA hB) (atom0895Coded_nonneg g hg hA hB)) (add_nonneg (atom0896Coded_nonneg g hg hA hB) (add_nonneg (atom0897Coded_nonneg g hg hA hB) (atom0898Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0899Coded_nonneg g hg hA hB) (atom0900Coded_nonneg g hg hA hB)) (add_nonneg (atom0901Coded_nonneg g hg hA hB) (add_nonneg (atom0902Coded_nonneg g hg hA hB) (atom0903Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0904Coded_nonneg g hg hA hB) (atom0905Coded_nonneg g hg hA hB)) (add_nonneg (atom0906Coded_nonneg g hg hA hB) (add_nonneg (atom0907Coded_nonneg g hg hA hB) (atom0908Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0909Coded_nonneg g hg hA hB) (atom0910Coded_nonneg g hg hA hB)) (add_nonneg (atom0911Coded_nonneg g hg hA hB) (add_nonneg (atom0912Coded_nonneg g hg hA hB) (atom0913Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0914Coded_nonneg g hg hA hB) (atom0915Coded_nonneg g hg hA hB)) (add_nonneg (atom0916Coded_nonneg g hg hA hB) (add_nonneg (atom0917Coded_nonneg g hg hA hB) (atom0918Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0919Coded_nonneg g hg hA hB) (atom0920Coded_nonneg g hg hA hB)) (add_nonneg (atom0921Coded_nonneg g hg hA hB) (add_nonneg (atom0922Coded_nonneg g hg hA hB) (atom0923Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0924Coded_nonneg g hg hA hB) (atom0925Coded_nonneg g hg hA hB)) (add_nonneg (atom0926Coded_nonneg g hg hA hB) (add_nonneg (atom0927Coded_nonneg g hg hA hB) (atom0928Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
