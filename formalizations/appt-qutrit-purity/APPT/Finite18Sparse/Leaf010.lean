import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0735 : SparsePolynomial.Poly := [([4,11,17], 1)]
theorem eval_atom0735 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0735 = ((g 4) * (g 11) * (g 17)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0735_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13537883520 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0735Coded : CoefficientMerge.Poly := [(1511, 1)]
theorem atom0735Coded_decode : atom0735 = SparsePolynomial.decodeCubic 18 atom0735Coded := by decide +kernel
theorem atom0735Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) := by
  have h := atom0735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0736 : SparsePolynomial.Poly := [([4,12,12], 1)]
theorem eval_atom0736 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4983552000 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736Coded : CoefficientMerge.Poly := [(1524, 1)]
theorem atom0736Coded_decode : atom0736 = SparsePolynomial.decodeCubic 18 atom0736Coded := by decide +kernel
theorem atom0736Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded) := by
  have h := atom0736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0737 : SparsePolynomial.Poly := [([4,12,13], 1)]
theorem eval_atom0737 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8680213920 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737Coded : CoefficientMerge.Poly := [(1525, 1)]
theorem atom0737Coded_decode : atom0737 = SparsePolynomial.decodeCubic 18 atom0737Coded := by decide +kernel
theorem atom0737Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) := by
  have h := atom0737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0738 : SparsePolynomial.Poly := [([4,12,14], 1)]
theorem eval_atom0738 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13712925600 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738Coded : CoefficientMerge.Poly := [(1526, 1)]
theorem atom0738Coded_decode : atom0738 = SparsePolynomial.decodeCubic 18 atom0738Coded := by decide +kernel
theorem atom0738Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) := by
  have h := atom0738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0739 : SparsePolynomial.Poly := [([4,12,15], 1)]
theorem eval_atom0739 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 4) * (g 12) * (g 15)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13122490080 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739Coded : CoefficientMerge.Poly := [(1527, 1)]
theorem atom0739Coded_decode : atom0739 = SparsePolynomial.decodeCubic 18 atom0739Coded := by decide +kernel
theorem atom0739Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded) := by
  have h := atom0739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0740 : SparsePolynomial.Poly := [([4,12,16], 1)]
theorem eval_atom0740 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 4) * (g 12) * (g 16)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9202835040 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740Coded : CoefficientMerge.Poly := [(1528, 1)]
theorem atom0740Coded_decode : atom0740 = SparsePolynomial.decodeCubic 18 atom0740Coded := by decide +kernel
theorem atom0740Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) := by
  have h := atom0740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0741 : SparsePolynomial.Poly := [([4,12,17], 1)]
theorem eval_atom0741 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 4) * (g 12) * (g 17)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14166482400 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741Coded : CoefficientMerge.Poly := [(1529, 1)]
theorem atom0741Coded_decode : atom0741 = SparsePolynomial.decodeCubic 18 atom0741Coded := by decide +kernel
theorem atom0741Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded) := by
  have h := atom0741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0742 : SparsePolynomial.Poly := [([4,13,13], 1)]
theorem eval_atom0742 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3690344448 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742Coded : CoefficientMerge.Poly := [(1543, 1)]
theorem atom0742Coded_decode : atom0742 = SparsePolynomial.decodeCubic 18 atom0742Coded := by decide +kernel
theorem atom0742Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) := by
  have h := atom0742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0743 : SparsePolynomial.Poly := [([4,13,14], 1)]
theorem eval_atom0743 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11120967960 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743Coded : CoefficientMerge.Poly := [(1544, 1)]
theorem atom0743Coded_decode : atom0743 = SparsePolynomial.decodeCubic 18 atom0743Coded := by decide +kernel
theorem atom0743Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) := by
  have h := atom0743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0744 : SparsePolynomial.Poly := [([4,13,15], 1)]
theorem eval_atom0744 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 4) * (g 13) * (g 15)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11594877840 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744Coded : CoefficientMerge.Poly := [(1545, 1)]
theorem atom0744Coded_decode : atom0744 = SparsePolynomial.decodeCubic 18 atom0744Coded := by decide +kernel
theorem atom0744Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded) := by
  have h := atom0744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0745 : SparsePolynomial.Poly := [([4,13,16], 1)]
theorem eval_atom0745 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 4) * (g 13) * (g 16)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8682470720 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745Coded : CoefficientMerge.Poly := [(1546, 1)]
theorem atom0745Coded_decode : atom0745 = SparsePolynomial.decodeCubic 18 atom0745Coded := by decide +kernel
theorem atom0745Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) := by
  have h := atom0745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0746 : SparsePolynomial.Poly := [([4,13,17], 1)]
theorem eval_atom0746 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 4) * (g 13) * (g 17)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10514692440 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746Coded : CoefficientMerge.Poly := [(1547, 1)]
theorem atom0746Coded_decode : atom0746 = SparsePolynomial.decodeCubic 18 atom0746Coded := by decide +kernel
theorem atom0746Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded) := by
  have h := atom0746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0747 : SparsePolynomial.Poly := [([4,14,14], 1)]
theorem eval_atom0747 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7996131000 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747Coded : CoefficientMerge.Poly := [(1562, 1)]
theorem atom0747Coded_decode : atom0747 = SparsePolynomial.decodeCubic 18 atom0747Coded := by decide +kernel
theorem atom0747Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) := by
  have h := atom0747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0748 : SparsePolynomial.Poly := [([4,14,15], 1)]
theorem eval_atom0748 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 4) * (g 14) * (g 15)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12540252120 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748Coded : CoefficientMerge.Poly := [(1563, 1)]
theorem atom0748Coded_decode : atom0748 = SparsePolynomial.decodeCubic 18 atom0748Coded := by decide +kernel
theorem atom0748Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) := by
  have h := atom0748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0749 : SparsePolynomial.Poly := [([4,14,16], 1)]
theorem eval_atom0749 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 4) * (g 14) * (g 16)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8869733360 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749Coded : CoefficientMerge.Poly := [(1564, 1)]
theorem atom0749Coded_decode : atom0749 = SparsePolynomial.decodeCubic 18 atom0749Coded := by decide +kernel
theorem atom0749Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded) := by
  have h := atom0749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0750 : SparsePolynomial.Poly := [([4,14,17], 1)]
theorem eval_atom0750 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 4) * (g 14) * (g 17)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11595222000 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750Coded : CoefficientMerge.Poly := [(1565, 1)]
theorem atom0750Coded_decode : atom0750 = SparsePolynomial.decodeCubic 18 atom0750Coded := by decide +kernel
theorem atom0750Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) := by
  have h := atom0750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0751 : SparsePolynomial.Poly := [([4,15,15], 1)]
theorem eval_atom0751 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3641223600 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751Coded : CoefficientMerge.Poly := [(1581, 1)]
theorem atom0751Coded_decode : atom0751 = SparsePolynomial.decodeCubic 18 atom0751Coded := by decide +kernel
theorem atom0751Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded) := by
  have h := atom0751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0752 : SparsePolynomial.Poly := [([4,15,16], 1)]
theorem eval_atom0752 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4763779440 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752Coded : CoefficientMerge.Poly := [(1582, 1)]
theorem atom0752Coded_decode : atom0752 = SparsePolynomial.decodeCubic 18 atom0752Coded := by decide +kernel
theorem atom0752Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) := by
  have h := atom0752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0753 : SparsePolynomial.Poly := [([4,15,17], 1)]
theorem eval_atom0753 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7669965240 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753Coded : CoefficientMerge.Poly := [(1583, 1)]
theorem atom0753Coded_decode : atom0753 = SparsePolynomial.decodeCubic 18 atom0753Coded := by decide +kernel
theorem atom0753Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) := by
  have h := atom0753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0754 : SparsePolynomial.Poly := [([4,16,17], 1)]
theorem eval_atom0754 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2648638440 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754Coded : CoefficientMerge.Poly := [(1601, 1)]
theorem atom0754Coded_decode : atom0754 = SparsePolynomial.decodeCubic 18 atom0754Coded := by decide +kernel
theorem atom0754Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded) := by
  have h := atom0754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0755 : SparsePolynomial.Poly := [([4,17,17], 1)]
theorem eval_atom0755 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2764487880 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755Coded : CoefficientMerge.Poly := [(1619, 1)]
theorem atom0755Coded_decode : atom0755 = SparsePolynomial.decodeCubic 18 atom0755Coded := by decide +kernel
theorem atom0755Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) := by
  have h := atom0755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0756 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom0756 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (580913280 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756Coded : CoefficientMerge.Poly := [(1715, 1)]
theorem atom0756Coded_decode : atom0756 = SparsePolynomial.decodeCubic 18 atom0756Coded := by decide +kernel
theorem atom0756Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (580913280 : Int) atom0756Coded) := by
  have h := atom0756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0757 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom0757 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (807960960 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757Coded : CoefficientMerge.Poly := [(1716, 1)]
theorem atom0757Coded_decode : atom0757 = SparsePolynomial.decodeCubic 18 atom0757Coded := by decide +kernel
theorem atom0757Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (807960960 : Int) atom0757Coded) := by
  have h := atom0757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0758 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom0758 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758Coded : CoefficientMerge.Poly := [(1717, 1)]
theorem atom0758Coded_decode : atom0758 = SparsePolynomial.decodeCubic 18 atom0758Coded := by decide +kernel
theorem atom0758Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0758Coded) := by
  have h := atom0758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0759 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom0759 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78704640 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759Coded : CoefficientMerge.Poly := [(1718, 1)]
theorem atom0759Coded_decode : atom0759 = SparsePolynomial.decodeCubic 18 atom0759Coded := by decide +kernel
theorem atom0759Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (78704640 : Int) atom0759Coded) := by
  have h := atom0759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0760 : SparsePolynomial.Poly := [([5,5,12], 1)]
theorem eval_atom0760 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (960689520 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760Coded : CoefficientMerge.Poly := [(1722, 1)]
theorem atom0760Coded_decode : atom0760 = SparsePolynomial.decodeCubic 18 atom0760Coded := by decide +kernel
theorem atom0760Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (960689520 : Int) atom0760Coded) := by
  have h := atom0760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0761 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom0761 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761Coded : CoefficientMerge.Poly := [(1734, 1)]
theorem atom0761Coded_decode : atom0761 = SparsePolynomial.decodeCubic 18 atom0761Coded := by decide +kernel
theorem atom0761Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (546687360 : Int) atom0761Coded) := by
  have h := atom0761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0762 : SparsePolynomial.Poly := [([5,6,10], 1)]
theorem eval_atom0762 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 5) * (g 6) * (g 10)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762Coded : CoefficientMerge.Poly := [(1738, 1)]
theorem atom0762Coded_decode : atom0762 = SparsePolynomial.decodeCubic 18 atom0762Coded := by decide +kernel
theorem atom0762Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0762Coded) := by
  have h := atom0762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0763 : SparsePolynomial.Poly := [([5,6,11], 1)]
theorem eval_atom0763 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 5) * (g 6) * (g 11)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763Coded : CoefficientMerge.Poly := [(1739, 1)]
theorem atom0763Coded_decode : atom0763 = SparsePolynomial.decodeCubic 18 atom0763Coded := by decide +kernel
theorem atom0763Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (207728640 : Int) atom0763Coded) := by
  have h := atom0763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0764 : SparsePolynomial.Poly := [([5,6,12], 1)]
theorem eval_atom0764 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 5) * (g 6) * (g 12)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1275597792 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764Coded : CoefficientMerge.Poly := [(1740, 1)]
theorem atom0764Coded_decode : atom0764 = SparsePolynomial.decodeCubic 18 atom0764Coded := by decide +kernel
theorem atom0764Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded) := by
  have h := atom0764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0765 : SparsePolynomial.Poly := [([5,6,14], 1)]
theorem eval_atom0765 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173304000 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765Coded : CoefficientMerge.Poly := [(1742, 1)]
theorem atom0765Coded_decode : atom0765 = SparsePolynomial.decodeCubic 18 atom0765Coded := by decide +kernel
theorem atom0765Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (173304000 : Int) atom0765Coded) := by
  have h := atom0765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0766 : SparsePolynomial.Poly := [([5,6,15], 1)]
theorem eval_atom0766 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766Coded : CoefficientMerge.Poly := [(1743, 1)]
theorem atom0766Coded_decode : atom0766 = SparsePolynomial.decodeCubic 18 atom0766Coded := by decide +kernel
theorem atom0766Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded) := by
  have h := atom0766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0767 : SparsePolynomial.Poly := [([5,6,16], 1)]
theorem eval_atom0767 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 5) * (g 6) * (g 16)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767Coded : CoefficientMerge.Poly := [(1744, 1)]
theorem atom0767Coded_decode : atom0767 = SparsePolynomial.decodeCubic 18 atom0767Coded := by decide +kernel
theorem atom0767Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) := by
  have h := atom0767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0768 : SparsePolynomial.Poly := [([5,6,17], 1)]
theorem eval_atom0768 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768Coded : CoefficientMerge.Poly := [(1745, 1)]
theorem atom0768Coded_decode : atom0768 = SparsePolynomial.decodeCubic 18 atom0768Coded := by decide +kernel
theorem atom0768Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) := by
  have h := atom0768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0769 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom0769 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126817920 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769Coded : CoefficientMerge.Poly := [(1753, 1)]
theorem atom0769Coded_decode : atom0769 = SparsePolynomial.decodeCubic 18 atom0769Coded := by decide +kernel
theorem atom0769Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (126817920 : Int) atom0769Coded) := by
  have h := atom0769_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0769Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0770 : SparsePolynomial.Poly := [([5,7,10], 1)]
theorem eval_atom0770 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0770 = ((g 5) * (g 7) * (g 10)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0770_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157409280 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770Coded : CoefficientMerge.Poly := [(1756, 1)]
theorem atom0770Coded_decode : atom0770 = SparsePolynomial.decodeCubic 18 atom0770Coded := by decide +kernel
theorem atom0770Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (157409280 : Int) atom0770Coded) := by
  have h := atom0770_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0770Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0771 : SparsePolynomial.Poly := [([5,7,11], 1)]
theorem eval_atom0771 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0771 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0771_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (314818560 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771Coded : CoefficientMerge.Poly := [(1757, 1)]
theorem atom0771Coded_decode : atom0771 = SparsePolynomial.decodeCubic 18 atom0771Coded := by decide +kernel
theorem atom0771Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (314818560 : Int) atom0771Coded) := by
  have h := atom0771_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0771Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0772 : SparsePolynomial.Poly := [([5,7,12], 1)]
theorem eval_atom0772 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0772 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0772_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1398790080 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772Coded : CoefficientMerge.Poly := [(1758, 1)]
theorem atom0772Coded_decode : atom0772 = SparsePolynomial.decodeCubic 18 atom0772Coded := by decide +kernel
theorem atom0772Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) := by
  have h := atom0772_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0772Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0773 : SparsePolynomial.Poly := [([5,7,13], 1)]
theorem eval_atom0773 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0773 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0773_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (748771920 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773Coded : CoefficientMerge.Poly := [(1759, 1)]
theorem atom0773Coded_decode : atom0773 = SparsePolynomial.decodeCubic 18 atom0773Coded := by decide +kernel
theorem atom0773Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (748771920 : Int) atom0773Coded) := by
  have h := atom0773_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0773Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0774 : SparsePolynomial.Poly := [([5,7,14], 1)]
theorem eval_atom0774 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0774 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0774_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1544502240 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774Coded : CoefficientMerge.Poly := [(1760, 1)]
theorem atom0774Coded_decode : atom0774 = SparsePolynomial.decodeCubic 18 atom0774Coded := by decide +kernel
theorem atom0774Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded) := by
  have h := atom0774_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0774Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0775 : SparsePolynomial.Poly := [([5,7,15], 1)]
theorem eval_atom0775 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0775 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0775_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3018304080 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775Coded : CoefficientMerge.Poly := [(1761, 1)]
theorem atom0775Coded_decode : atom0775 = SparsePolynomial.decodeCubic 18 atom0775Coded := by decide +kernel
theorem atom0775Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) := by
  have h := atom0775_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0775Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0776 : SparsePolynomial.Poly := [([5,7,16], 1)]
theorem eval_atom0776 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0776 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0776_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4822144560 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776Coded : CoefficientMerge.Poly := [(1762, 1)]
theorem atom0776Coded_decode : atom0776 = SparsePolynomial.decodeCubic 18 atom0776Coded := by decide +kernel
theorem atom0776Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded) := by
  have h := atom0776_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0776Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0777 : SparsePolynomial.Poly := [([5,7,17], 1)]
theorem eval_atom0777 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0777 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0777_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6797629440 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777Coded : CoefficientMerge.Poly := [(1763, 1)]
theorem atom0777Coded_decode : atom0777 = SparsePolynomial.decodeCubic 18 atom0777Coded := by decide +kernel
theorem atom0777Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) := by
  have h := atom0777_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0777Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0778 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom0778 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778Coded : CoefficientMerge.Poly := [(1772, 1)]
theorem atom0778Coded_decode : atom0778 = SparsePolynomial.decodeCubic 18 atom0778Coded := by decide +kernel
theorem atom0778Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (546687360 : Int) atom0778Coded) := by
  have h := atom0778_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0778Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0779 : SparsePolynomial.Poly := [([5,8,9], 1)]
theorem eval_atom0779 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0779 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0779_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (832953600 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779Coded : CoefficientMerge.Poly := [(1773, 1)]
theorem atom0779Coded_decode : atom0779 = SparsePolynomial.decodeCubic 18 atom0779Coded := by decide +kernel
theorem atom0779Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (832953600 : Int) atom0779Coded) := by
  have h := atom0779_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0779Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0780 : SparsePolynomial.Poly := [([5,8,10], 1)]
theorem eval_atom0780 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0780 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0780_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (993588480 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780Coded : CoefficientMerge.Poly := [(1774, 1)]
theorem atom0780Coded_decode : atom0780 = SparsePolynomial.decodeCubic 18 atom0780Coded := by decide +kernel
theorem atom0780Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (993588480 : Int) atom0780Coded) := by
  have h := atom0780_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0780Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0781 : SparsePolynomial.Poly := [([5,8,11], 1)]
theorem eval_atom0781 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0781 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0781_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1154223360 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781Coded : CoefficientMerge.Poly := [(1775, 1)]
theorem atom0781Coded_decode : atom0781 = SparsePolynomial.decodeCubic 18 atom0781Coded := by decide +kernel
theorem atom0781Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded) := by
  have h := atom0781_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0781Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0782 : SparsePolynomial.Poly := [([5,8,12], 1)]
theorem eval_atom0782 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0782 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0782_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2225592000 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782Coded : CoefficientMerge.Poly := [(1776, 1)]
theorem atom0782Coded_decode : atom0782 = SparsePolynomial.decodeCubic 18 atom0782Coded := by decide +kernel
theorem atom0782Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) := by
  have h := atom0782_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0782Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0783 : SparsePolynomial.Poly := [([5,8,13], 1)]
theorem eval_atom0783 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0783 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0783_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1908204720 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783Coded : CoefficientMerge.Poly := [(1777, 1)]
theorem atom0783Coded_decode : atom0783 = SparsePolynomial.decodeCubic 18 atom0783Coded := by decide +kernel
theorem atom0783Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) := by
  have h := atom0783_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0783Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0784 : SparsePolynomial.Poly := [([5,8,14], 1)]
theorem eval_atom0784 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0784 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0784_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3183133920 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784Coded : CoefficientMerge.Poly := [(1778, 1)]
theorem atom0784Coded_decode : atom0784 = SparsePolynomial.decodeCubic 18 atom0784Coded := by decide +kernel
theorem atom0784Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded) := by
  have h := atom0784_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0784Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0785 : SparsePolynomial.Poly := [([5,8,15], 1)]
theorem eval_atom0785 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0785 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0785_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4551344880 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785Coded : CoefficientMerge.Poly := [(1779, 1)]
theorem atom0785Coded_decode : atom0785 = SparsePolynomial.decodeCubic 18 atom0785Coded := by decide +kernel
theorem atom0785Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) := by
  have h := atom0785_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0785Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0786 : SparsePolynomial.Poly := [([5,8,16], 1)]
theorem eval_atom0786 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0786 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0786_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6551182800 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786Coded : CoefficientMerge.Poly := [(1780, 1)]
theorem atom0786Coded_decode : atom0786 = SparsePolynomial.decodeCubic 18 atom0786Coded := by decide +kernel
theorem atom0786Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded) := by
  have h := atom0786_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0786Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0787 : SparsePolynomial.Poly := [([5,8,17], 1)]
theorem eval_atom0787 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0787 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0787_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8696665440 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787Coded : CoefficientMerge.Poly := [(1781, 1)]
theorem atom0787Coded_decode : atom0787 = SparsePolynomial.decodeCubic 18 atom0787Coded := by decide +kernel
theorem atom0787Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) := by
  have h := atom0787_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0787Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0788 : SparsePolynomial.Poly := [([5,9,9], 1)]
theorem eval_atom0788 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1063635840 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788Coded : CoefficientMerge.Poly := [(1791, 1)]
theorem atom0788Coded_decode : atom0788 = SparsePolynomial.decodeCubic 18 atom0788Coded := by decide +kernel
theorem atom0788Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) := by
  have h := atom0788_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0788Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0789 : SparsePolynomial.Poly := [([5,9,10], 1)]
theorem eval_atom0789 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0789 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0789_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1890097920 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789Coded : CoefficientMerge.Poly := [(1792, 1)]
theorem atom0789Coded_decode : atom0789 = SparsePolynomial.decodeCubic 18 atom0789Coded := by decide +kernel
theorem atom0789Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded) := by
  have h := atom0789_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0789Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0790 : SparsePolynomial.Poly := [([5,9,11], 1)]
theorem eval_atom0790 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0790 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0790_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2003639040 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790Coded : CoefficientMerge.Poly := [(1793, 1)]
theorem atom0790Coded_decode : atom0790 = SparsePolynomial.decodeCubic 18 atom0790Coded := by decide +kernel
theorem atom0790Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) := by
  have h := atom0790_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0790Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0791 : SparsePolynomial.Poly := [([5,9,12], 1)]
theorem eval_atom0791 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0791 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0791_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3152367360 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791Coded : CoefficientMerge.Poly := [(1794, 1)]
theorem atom0791Coded_decode : atom0791 = SparsePolynomial.decodeCubic 18 atom0791Coded := by decide +kernel
theorem atom0791Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded) := by
  have h := atom0791_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0791Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0792 : SparsePolynomial.Poly := [([5,9,13], 1)]
theorem eval_atom0792 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0792 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0792_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2936154480 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792Coded : CoefficientMerge.Poly := [(1795, 1)]
theorem atom0792Coded_decode : atom0792 = SparsePolynomial.decodeCubic 18 atom0792Coded := by decide +kernel
theorem atom0792Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) := by
  have h := atom0792_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0792Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0793 : SparsePolynomial.Poly := [([5,9,14], 1)]
theorem eval_atom0793 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0793 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0793_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4697875680 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793Coded : CoefficientMerge.Poly := [(1796, 1)]
theorem atom0793Coded_decode : atom0793 = SparsePolynomial.decodeCubic 18 atom0793Coded := by decide +kernel
theorem atom0793Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) := by
  have h := atom0793_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0793Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0794 : SparsePolynomial.Poly := [([5,9,15], 1)]
theorem eval_atom0794 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0794 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0794_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5778953520 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794Coded : CoefficientMerge.Poly := [(1797, 1)]
theorem atom0794Coded_decode : atom0794 = SparsePolynomial.decodeCubic 18 atom0794Coded := by decide +kernel
theorem atom0794Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded) := by
  have h := atom0794_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0794Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0795 : SparsePolynomial.Poly := [([5,9,16], 1)]
theorem eval_atom0795 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0795 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0795_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7877275920 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795Coded : CoefficientMerge.Poly := [(1798, 1)]
theorem atom0795Coded_decode : atom0795 = SparsePolynomial.decodeCubic 18 atom0795Coded := by decide +kernel
theorem atom0795Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) := by
  have h := atom0795_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0795Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0796 : SparsePolynomial.Poly := [([5,9,17], 1)]
theorem eval_atom0796 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0796 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0796_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10096083360 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796Coded : CoefficientMerge.Poly := [(1799, 1)]
theorem atom0796Coded_decode : atom0796 = SparsePolynomial.decodeCubic 18 atom0796Coded := by decide +kernel
theorem atom0796Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded) := by
  have h := atom0796_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0796Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0797 : SparsePolynomial.Poly := [([5,10,10], 1)]
theorem eval_atom0797 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1707696000 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797Coded : CoefficientMerge.Poly := [(1810, 1)]
theorem atom0797Coded_decode : atom0797 = SparsePolynomial.decodeCubic 18 atom0797Coded := by decide +kernel
theorem atom0797Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) := by
  have h := atom0797_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0797Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0798 : SparsePolynomial.Poly := [([5,10,11], 1)]
theorem eval_atom0798 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0798 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0798_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3097532160 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798Coded : CoefficientMerge.Poly := [(1811, 1)]
theorem atom0798Coded_decode : atom0798 = SparsePolynomial.decodeCubic 18 atom0798Coded := by decide +kernel
theorem atom0798Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) := by
  have h := atom0798_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0798Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0799 : SparsePolynomial.Poly := [([5,10,12], 1)]
theorem eval_atom0799 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0799 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0799_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4211694720 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799Coded : CoefficientMerge.Poly := [(1812, 1)]
theorem atom0799Coded_decode : atom0799 = SparsePolynomial.decodeCubic 18 atom0799Coded := by decide +kernel
theorem atom0799Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded) := by
  have h := atom0799_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0799Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0800 : SparsePolynomial.Poly := [([5,10,13], 1)]
theorem eval_atom0800 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0800 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0800_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3949897200 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800Coded : CoefficientMerge.Poly := [(1813, 1)]
theorem atom0800Coded_decode : atom0800 = SparsePolynomial.decodeCubic 18 atom0800Coded := by decide +kernel
theorem atom0800Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) := by
  have h := atom0800_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0800Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0801 : SparsePolynomial.Poly := [([5,10,14], 1)]
theorem eval_atom0801 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0801 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0801_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6236164320 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801Coded : CoefficientMerge.Poly := [(1814, 1)]
theorem atom0801Coded_decode : atom0801 = SparsePolynomial.decodeCubic 18 atom0801Coded := by decide +kernel
theorem atom0801Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded) := by
  have h := atom0801_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0801Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0802 : SparsePolynomial.Poly := [([5,10,15], 1)]
theorem eval_atom0802 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0802 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0802_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6642556080 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802Coded : CoefficientMerge.Poly := [(1815, 1)]
theorem atom0802Coded_decode : atom0802 = SparsePolynomial.decodeCubic 18 atom0802Coded := by decide +kernel
theorem atom0802Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) := by
  have h := atom0802_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0802Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0803 : SparsePolynomial.Poly := [([5,10,16], 1)]
theorem eval_atom0803 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0803 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0803_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8636322960 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803Coded : CoefficientMerge.Poly := [(1816, 1)]
theorem atom0803Coded_decode : atom0803 = SparsePolynomial.decodeCubic 18 atom0803Coded := by decide +kernel
theorem atom0803Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) := by
  have h := atom0803_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0803Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0804 : SparsePolynomial.Poly := [([5,10,17], 1)]
theorem eval_atom0804 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0804 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0804_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11022864480 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804Coded : CoefficientMerge.Poly := [(1817, 1)]
theorem atom0804Coded_decode : atom0804 = SparsePolynomial.decodeCubic 18 atom0804Coded := by decide +kernel
theorem atom0804Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded) := by
  have h := atom0804_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0804Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0805 : SparsePolynomial.Poly := [([5,11,11], 1)]
theorem eval_atom0805 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2604689280 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805Coded : CoefficientMerge.Poly := [(1829, 1)]
theorem atom0805Coded_decode : atom0805 = SparsePolynomial.decodeCubic 18 atom0805Coded := by decide +kernel
theorem atom0805Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) := by
  have h := atom0805_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0805Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0806 : SparsePolynomial.Poly := [([5,11,12], 1)]
theorem eval_atom0806 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0806 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0806_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5147904960 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806Coded : CoefficientMerge.Poly := [(1830, 1)]
theorem atom0806Coded_decode : atom0806 = SparsePolynomial.decodeCubic 18 atom0806Coded := by decide +kernel
theorem atom0806Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded) := by
  have h := atom0806_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0806Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0807 : SparsePolynomial.Poly := [([5,11,13], 1)]
theorem eval_atom0807 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0807 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0807_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4759343280 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807Coded : CoefficientMerge.Poly := [(1831, 1)]
theorem atom0807Coded_decode : atom0807 = SparsePolynomial.decodeCubic 18 atom0807Coded := by decide +kernel
theorem atom0807Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) := by
  have h := atom0807_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0807Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0808 : SparsePolynomial.Poly := [([5,11,14], 1)]
theorem eval_atom0808 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0808 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0808_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7588308960 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808Coded : CoefficientMerge.Poly := [(1832, 1)]
theorem atom0808Coded_decode : atom0808 = SparsePolynomial.decodeCubic 18 atom0808Coded := by decide +kernel
theorem atom0808Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) := by
  have h := atom0808_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0808Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0809 : SparsePolynomial.Poly := [([5,11,15], 1)]
theorem eval_atom0809 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0809 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0809_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8197968240 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809Coded : CoefficientMerge.Poly := [(1833, 1)]
theorem atom0809Coded_decode : atom0809 = SparsePolynomial.decodeCubic 18 atom0809Coded := by decide +kernel
theorem atom0809Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded) := by
  have h := atom0809_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0809Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0810 : SparsePolynomial.Poly := [([5,11,16], 1)]
theorem eval_atom0810 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0810 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0810_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8997500880 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810Coded : CoefficientMerge.Poly := [(1834, 1)]
theorem atom0810Coded_decode : atom0810 = SparsePolynomial.decodeCubic 18 atom0810Coded := by decide +kernel
theorem atom0810Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) := by
  have h := atom0810_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0810Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0811 : SparsePolynomial.Poly := [([5,11,17], 1)]
theorem eval_atom0811 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0811 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0811_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13443213600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811Coded : CoefficientMerge.Poly := [(1835, 1)]
theorem atom0811Coded_decode : atom0811 = SparsePolynomial.decodeCubic 18 atom0811Coded := by decide +kernel
theorem atom0811Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded) := by
  have h := atom0811_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0811Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0812 : SparsePolynomial.Poly := [([5,12,12], 1)]
theorem eval_atom0812 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4203601920 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812Coded : CoefficientMerge.Poly := [(1848, 1)]
theorem atom0812Coded_decode : atom0812 = SparsePolynomial.decodeCubic 18 atom0812Coded := by decide +kernel
theorem atom0812Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) := by
  have h := atom0812_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0812Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0813 : SparsePolynomial.Poly := [([5,12,13], 1)]
theorem eval_atom0813 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0813 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0813_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7777390680 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813Coded : CoefficientMerge.Poly := [(1849, 1)]
theorem atom0813Coded_decode : atom0813 = SparsePolynomial.decodeCubic 18 atom0813Coded := by decide +kernel
theorem atom0813Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) := by
  have h := atom0813_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0813Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0814 : SparsePolynomial.Poly := [([5,12,14], 1)]
theorem eval_atom0814 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0814 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0814_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12945232800 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814Coded : CoefficientMerge.Poly := [(1850, 1)]
theorem atom0814Coded_decode : atom0814 = SparsePolynomial.decodeCubic 18 atom0814Coded := by decide +kernel
theorem atom0814Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded) := by
  have h := atom0814_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0814Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block010 : CoefficientMerge.Poly := [(1511, 13537883520), (1524, 4983552000), (1525, 8680213920), (1526, 13712925600), (1527, 13122490080), (1528, 9202835040), (1529, 14166482400), (1543, 3690344448), (1544, 11120967960), (1545, 11594877840), (1546, 8682470720), (1547, 10514692440), (1562, 7996131000), (1563, 12540252120), (1564, 8869733360), (1565, 11595222000), (1581, 3641223600), (1582, 4763779440), (1583, 7669965240), (1601, 2648638440), (1619, 2764487880), (1715, 580913280), (1716, 807960960), (1717, 103864320), (1718, 78704640), (1722, 960689520), (1734, 546687360), (1738, 103864320), (1739, 207728640), (1740, 1275597792), (1742, 173304000), (1743, 1180247040), (1744, 2293143552), (1745, 3586383360), (1753, 126817920), (1756, 157409280), (1757, 314818560), (1758, 1398790080), (1759, 748771920), (1760, 1544502240), (1761, 3018304080), (1762, 4822144560), (1763, 6797629440), (1772, 546687360), (1773, 832953600), (1774, 993588480), (1775, 1154223360), (1776, 2225592000), (1777, 1908204720), (1778, 3183133920), (1779, 4551344880), (1780, 6551182800), (1781, 8696665440), (1791, 1063635840), (1792, 1890097920), (1793, 2003639040), (1794, 3152367360), (1795, 2936154480), (1796, 4697875680), (1797, 5778953520), (1798, 7877275920), (1799, 10096083360), (1810, 1707696000), (1811, 3097532160), (1812, 4211694720), (1813, 3949897200), (1814, 6236164320), (1815, 6642556080), (1816, 8636322960), (1817, 11022864480), (1829, 2604689280), (1830, 5147904960), (1831, 4759343280), (1832, 7588308960), (1833, 8197968240), (1834, 8997500880), (1835, 13443213600), (1848, 4203601920), (1849, 7777390680), (1850, 12945232800)]
theorem block010_data : block010 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)))))))) := by decide +kernel
theorem block010_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block010 := by
  rw [block010_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0735Coded_nonneg g hg hA hB) (atom0736Coded_nonneg g hg hA hB)) (add_nonneg (atom0737Coded_nonneg g hg hA hB) (add_nonneg (atom0738Coded_nonneg g hg hA hB) (atom0739Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0740Coded_nonneg g hg hA hB) (atom0741Coded_nonneg g hg hA hB)) (add_nonneg (atom0742Coded_nonneg g hg hA hB) (add_nonneg (atom0743Coded_nonneg g hg hA hB) (atom0744Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0745Coded_nonneg g hg hA hB) (atom0746Coded_nonneg g hg hA hB)) (add_nonneg (atom0747Coded_nonneg g hg hA hB) (add_nonneg (atom0748Coded_nonneg g hg hA hB) (atom0749Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0750Coded_nonneg g hg hA hB) (atom0751Coded_nonneg g hg hA hB)) (add_nonneg (atom0752Coded_nonneg g hg hA hB) (add_nonneg (atom0753Coded_nonneg g hg hA hB) (atom0754Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0755Coded_nonneg g hg hA hB) (atom0756Coded_nonneg g hg hA hB)) (add_nonneg (atom0757Coded_nonneg g hg hA hB) (add_nonneg (atom0758Coded_nonneg g hg hA hB) (atom0759Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0760Coded_nonneg g hg hA hB) (atom0761Coded_nonneg g hg hA hB)) (add_nonneg (atom0762Coded_nonneg g hg hA hB) (add_nonneg (atom0763Coded_nonneg g hg hA hB) (atom0764Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0765Coded_nonneg g hg hA hB) (atom0766Coded_nonneg g hg hA hB)) (add_nonneg (atom0767Coded_nonneg g hg hA hB) (add_nonneg (atom0768Coded_nonneg g hg hA hB) (atom0769Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0770Coded_nonneg g hg hA hB) (atom0771Coded_nonneg g hg hA hB)) (add_nonneg (atom0772Coded_nonneg g hg hA hB) (add_nonneg (atom0773Coded_nonneg g hg hA hB) (atom0774Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0775Coded_nonneg g hg hA hB) (atom0776Coded_nonneg g hg hA hB)) (add_nonneg (atom0777Coded_nonneg g hg hA hB) (add_nonneg (atom0778Coded_nonneg g hg hA hB) (atom0779Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0780Coded_nonneg g hg hA hB) (atom0781Coded_nonneg g hg hA hB)) (add_nonneg (atom0782Coded_nonneg g hg hA hB) (add_nonneg (atom0783Coded_nonneg g hg hA hB) (atom0784Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0785Coded_nonneg g hg hA hB) (atom0786Coded_nonneg g hg hA hB)) (add_nonneg (atom0787Coded_nonneg g hg hA hB) (add_nonneg (atom0788Coded_nonneg g hg hA hB) (atom0789Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0790Coded_nonneg g hg hA hB) (atom0791Coded_nonneg g hg hA hB)) (add_nonneg (atom0792Coded_nonneg g hg hA hB) (add_nonneg (atom0793Coded_nonneg g hg hA hB) (atom0794Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0795Coded_nonneg g hg hA hB) (atom0796Coded_nonneg g hg hA hB)) (add_nonneg (atom0797Coded_nonneg g hg hA hB) (add_nonneg (atom0798Coded_nonneg g hg hA hB) (atom0799Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0800Coded_nonneg g hg hA hB) (atom0801Coded_nonneg g hg hA hB)) (add_nonneg (atom0802Coded_nonneg g hg hA hB) (add_nonneg (atom0803Coded_nonneg g hg hA hB) (atom0804Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0805Coded_nonneg g hg hA hB) (atom0806Coded_nonneg g hg hA hB)) (add_nonneg (atom0807Coded_nonneg g hg hA hB) (add_nonneg (atom0808Coded_nonneg g hg hA hB) (atom0809Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0810Coded_nonneg g hg hA hB) (atom0811Coded_nonneg g hg hA hB)) (add_nonneg (atom0812Coded_nonneg g hg hA hB) (add_nonneg (atom0813Coded_nonneg g hg hA hB) (atom0814Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
