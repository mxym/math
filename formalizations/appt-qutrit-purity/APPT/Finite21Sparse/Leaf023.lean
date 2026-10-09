import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1696 : SparsePolynomial.Poly := [([14,15,17], 1)]
theorem eval_atom1696 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1696 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom1696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1696_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49533129676800 : Int) atom1696) := by
  rw [SparsePolynomial.eval_scale, eval_atom1696]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1696Coded : CoefficientMerge.Poly := [(6506, 1)]
theorem atom1696Coded_decode : atom1696 = SparsePolynomial.decodeCubic 21 atom1696Coded := by decide +kernel
theorem atom1696Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49533129676800 : Int) atom1696Coded) := by
  have h := atom1696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1697 : SparsePolynomial.Poly := [([14,15,18], 1)]
theorem eval_atom1697 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1697 = ((g 14) * (g 15) * (g 18)) := by
  norm_num [atom1697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1697_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59532643699200 : Int) atom1697) := by
  rw [SparsePolynomial.eval_scale, eval_atom1697]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1697Coded : CoefficientMerge.Poly := [(6507, 1)]
theorem atom1697Coded_decode : atom1697 = SparsePolynomial.decodeCubic 21 atom1697Coded := by decide +kernel
theorem atom1697Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59532643699200 : Int) atom1697Coded) := by
  have h := atom1697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1698 : SparsePolynomial.Poly := [([14,15,19], 1)]
theorem eval_atom1698 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1698 = ((g 14) * (g 15) * (g 19)) := by
  norm_num [atom1698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1698_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43553022105600 : Int) atom1698) := by
  rw [SparsePolynomial.eval_scale, eval_atom1698]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1698Coded : CoefficientMerge.Poly := [(6508, 1)]
theorem atom1698Coded_decode : atom1698 = SparsePolynomial.decodeCubic 21 atom1698Coded := by decide +kernel
theorem atom1698Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43553022105600 : Int) atom1698Coded) := by
  have h := atom1698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1699 : SparsePolynomial.Poly := [([14,15,20], 1)]
theorem eval_atom1699 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1699 = ((g 14) * (g 15) * (g 20)) := by
  norm_num [atom1699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1699_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85602216268800 : Int) atom1699) := by
  rw [SparsePolynomial.eval_scale, eval_atom1699]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1699Coded : CoefficientMerge.Poly := [(6509, 1)]
theorem atom1699Coded_decode : atom1699 = SparsePolynomial.decodeCubic 21 atom1699Coded := by decide +kernel
theorem atom1699Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (85602216268800 : Int) atom1699Coded) := by
  have h := atom1699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1700 : SparsePolynomial.Poly := [([14,16,16], 1)]
theorem eval_atom1700 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1700 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom1700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1700_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4836604469760 : Int) atom1700) := by
  rw [SparsePolynomial.eval_scale, eval_atom1700]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1700Coded : CoefficientMerge.Poly := [(6526, 1)]
theorem atom1700Coded_decode : atom1700 = SparsePolynomial.decodeCubic 21 atom1700Coded := by decide +kernel
theorem atom1700Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4836604469760 : Int) atom1700Coded) := by
  have h := atom1700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1701 : SparsePolynomial.Poly := [([14,16,17], 1)]
theorem eval_atom1701 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1701 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom1701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1701_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47815814592000 : Int) atom1701) := by
  rw [SparsePolynomial.eval_scale, eval_atom1701]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1701Coded : CoefficientMerge.Poly := [(6527, 1)]
theorem atom1701Coded_decode : atom1701 = SparsePolynomial.decodeCubic 21 atom1701Coded := by decide +kernel
theorem atom1701Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47815814592000 : Int) atom1701Coded) := by
  have h := atom1701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1702 : SparsePolynomial.Poly := [([14,16,18], 1)]
theorem eval_atom1702 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1702 = ((g 14) * (g 16) * (g 18)) := by
  norm_num [atom1702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1702_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68387445504000 : Int) atom1702) := by
  rw [SparsePolynomial.eval_scale, eval_atom1702]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1702Coded : CoefficientMerge.Poly := [(6528, 1)]
theorem atom1702Coded_decode : atom1702 = SparsePolynomial.decodeCubic 21 atom1702Coded := by decide +kernel
theorem atom1702Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68387445504000 : Int) atom1702Coded) := by
  have h := atom1702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1703 : SparsePolynomial.Poly := [([14,16,19], 1)]
theorem eval_atom1703 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1703 = ((g 14) * (g 16) * (g 19)) := by
  norm_num [atom1703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1703_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63497105280000 : Int) atom1703) := by
  rw [SparsePolynomial.eval_scale, eval_atom1703]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1703Coded : CoefficientMerge.Poly := [(6529, 1)]
theorem atom1703Coded_decode : atom1703 = SparsePolynomial.decodeCubic 21 atom1703Coded := by decide +kernel
theorem atom1703Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63497105280000 : Int) atom1703Coded) := by
  have h := atom1703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1704 : SparsePolynomial.Poly := [([14,16,20], 1)]
theorem eval_atom1704 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1704 = ((g 14) * (g 16) * (g 20)) := by
  norm_num [atom1704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1704_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91041511680000 : Int) atom1704) := by
  rw [SparsePolynomial.eval_scale, eval_atom1704]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1704Coded : CoefficientMerge.Poly := [(6530, 1)]
theorem atom1704Coded_decode : atom1704 = SparsePolynomial.decodeCubic 21 atom1704Coded := by decide +kernel
theorem atom1704Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (91041511680000 : Int) atom1704Coded) := by
  have h := atom1704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1705 : SparsePolynomial.Poly := [([14,17,17], 1)]
theorem eval_atom1705 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1705 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom1705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1705_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39020933952000 : Int) atom1705) := by
  rw [SparsePolynomial.eval_scale, eval_atom1705]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1705Coded : CoefficientMerge.Poly := [(6548, 1)]
theorem atom1705Coded_decode : atom1705 = SparsePolynomial.decodeCubic 21 atom1705Coded := by decide +kernel
theorem atom1705Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39020933952000 : Int) atom1705Coded) := by
  have h := atom1705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1706 : SparsePolynomial.Poly := [([14,17,18], 1)]
theorem eval_atom1706 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1706 = ((g 14) * (g 17) * (g 18)) := by
  norm_num [atom1706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1706_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84087448704000 : Int) atom1706) := by
  rw [SparsePolynomial.eval_scale, eval_atom1706]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1706Coded : CoefficientMerge.Poly := [(6549, 1)]
theorem atom1706Coded_decode : atom1706 = SparsePolynomial.decodeCubic 21 atom1706Coded := by decide +kernel
theorem atom1706Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84087448704000 : Int) atom1706Coded) := by
  have h := atom1706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1707 : SparsePolynomial.Poly := [([14,17,19], 1)]
theorem eval_atom1707 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1707 = ((g 14) * (g 17) * (g 19)) := by
  norm_num [atom1707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1707_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82236760704000 : Int) atom1707) := by
  rw [SparsePolynomial.eval_scale, eval_atom1707]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1707Coded : CoefficientMerge.Poly := [(6550, 1)]
theorem atom1707Coded_decode : atom1707 = SparsePolynomial.decodeCubic 21 atom1707Coded := by decide +kernel
theorem atom1707Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82236760704000 : Int) atom1707Coded) := by
  have h := atom1707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1708 : SparsePolynomial.Poly := [([14,17,20], 1)]
theorem eval_atom1708 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1708 = ((g 14) * (g 17) * (g 20)) := by
  norm_num [atom1708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1708_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98579775168000 : Int) atom1708) := by
  rw [SparsePolynomial.eval_scale, eval_atom1708]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1708Coded : CoefficientMerge.Poly := [(6551, 1)]
theorem atom1708Coded_decode : atom1708 = SparsePolynomial.decodeCubic 21 atom1708Coded := by decide +kernel
theorem atom1708Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (98579775168000 : Int) atom1708Coded) := by
  have h := atom1708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1709 : SparsePolynomial.Poly := [([14,18,18], 1)]
theorem eval_atom1709 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1709 = ((g 14) * (g 18) * (g 18)) := by
  norm_num [atom1709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1709_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38658816000000 : Int) atom1709) := by
  rw [SparsePolynomial.eval_scale, eval_atom1709]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1709Coded : CoefficientMerge.Poly := [(6570, 1)]
theorem atom1709Coded_decode : atom1709 = SparsePolynomial.decodeCubic 21 atom1709Coded := by decide +kernel
theorem atom1709Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38658816000000 : Int) atom1709Coded) := by
  have h := atom1709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1710 : SparsePolynomial.Poly := [([14,18,19], 1)]
theorem eval_atom1710 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1710 = ((g 14) * (g 18) * (g 19)) := by
  norm_num [atom1710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1710_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85996536192000 : Int) atom1710) := by
  rw [SparsePolynomial.eval_scale, eval_atom1710]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1710Coded : CoefficientMerge.Poly := [(6571, 1)]
theorem atom1710Coded_decode : atom1710 = SparsePolynomial.decodeCubic 21 atom1710Coded := by decide +kernel
theorem atom1710Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (85996536192000 : Int) atom1710Coded) := by
  have h := atom1710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1711 : SparsePolynomial.Poly := [([14,18,20], 1)]
theorem eval_atom1711 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1711 = ((g 14) * (g 18) * (g 20)) := by
  norm_num [atom1711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1711_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104862038400000 : Int) atom1711) := by
  rw [SparsePolynomial.eval_scale, eval_atom1711]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1711Coded : CoefficientMerge.Poly := [(6572, 1)]
theorem atom1711Coded_decode : atom1711 = SparsePolynomial.decodeCubic 21 atom1711Coded := by decide +kernel
theorem atom1711Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (104862038400000 : Int) atom1711Coded) := by
  have h := atom1711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1712 : SparsePolynomial.Poly := [([14,19,19], 1)]
theorem eval_atom1712 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1712 = ((g 14) * (g 19) * (g 19)) := by
  norm_num [atom1712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1712_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44360991360000 : Int) atom1712) := by
  rw [SparsePolynomial.eval_scale, eval_atom1712]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1712Coded : CoefficientMerge.Poly := [(6592, 1)]
theorem atom1712Coded_decode : atom1712 = SparsePolynomial.decodeCubic 21 atom1712Coded := by decide +kernel
theorem atom1712Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44360991360000 : Int) atom1712Coded) := by
  have h := atom1712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1713 : SparsePolynomial.Poly := [([14,19,20], 1)]
theorem eval_atom1713 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1713 = ((g 14) * (g 19) * (g 20)) := by
  norm_num [atom1713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1713_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110109972672000 : Int) atom1713) := by
  rw [SparsePolynomial.eval_scale, eval_atom1713]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1713Coded : CoefficientMerge.Poly := [(6593, 1)]
theorem atom1713Coded_decode : atom1713 = SparsePolynomial.decodeCubic 21 atom1713Coded := by decide +kernel
theorem atom1713Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (110109972672000 : Int) atom1713Coded) := by
  have h := atom1713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1714 : SparsePolynomial.Poly := [([14,20,20], 1)]
theorem eval_atom1714 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1714 = ((g 14) * (g 20) * (g 20)) := by
  norm_num [atom1714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1714_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59341282560000 : Int) atom1714) := by
  rw [SparsePolynomial.eval_scale, eval_atom1714]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1714Coded : CoefficientMerge.Poly := [(6614, 1)]
theorem atom1714Coded_decode : atom1714 = SparsePolynomial.decodeCubic 21 atom1714Coded := by decide +kernel
theorem atom1714Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59341282560000 : Int) atom1714Coded) := by
  have h := atom1714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1715 : SparsePolynomial.Poly := [([15,15,15], 1)]
theorem eval_atom1715 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1715 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom1715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1715_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (966470400000 : Int) atom1715) := by
  rw [SparsePolynomial.eval_scale, eval_atom1715]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1715Coded : CoefficientMerge.Poly := [(6945, 1)]
theorem atom1715Coded_decode : atom1715 = SparsePolynomial.decodeCubic 21 atom1715Coded := by decide +kernel
theorem atom1715Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (966470400000 : Int) atom1715Coded) := by
  have h := atom1715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1716 : SparsePolynomial.Poly := [([15,15,16], 1)]
theorem eval_atom1716 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1716 = ((g 15) * (g 15) * (g 16)) := by
  norm_num [atom1716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1716_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7720165555200 : Int) atom1716) := by
  rw [SparsePolynomial.eval_scale, eval_atom1716]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1716Coded : CoefficientMerge.Poly := [(6946, 1)]
theorem atom1716Coded_decode : atom1716 = SparsePolynomial.decodeCubic 21 atom1716Coded := by decide +kernel
theorem atom1716Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7720165555200 : Int) atom1716Coded) := by
  have h := atom1716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1717 : SparsePolynomial.Poly := [([15,15,17], 1)]
theorem eval_atom1717 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1717 = ((g 15) * (g 15) * (g 17)) := by
  norm_num [atom1717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1717_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28555128806400 : Int) atom1717) := by
  rw [SparsePolynomial.eval_scale, eval_atom1717]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1717Coded : CoefficientMerge.Poly := [(6947, 1)]
theorem atom1717Coded_decode : atom1717 = SparsePolynomial.decodeCubic 21 atom1717Coded := by decide +kernel
theorem atom1717Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28555128806400 : Int) atom1717Coded) := by
  have h := atom1717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1718 : SparsePolynomial.Poly := [([15,15,18], 1)]
theorem eval_atom1718 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1718 = ((g 15) * (g 15) * (g 18)) := by
  norm_num [atom1718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1718_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34410212121600 : Int) atom1718) := by
  rw [SparsePolynomial.eval_scale, eval_atom1718]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1718Coded : CoefficientMerge.Poly := [(6948, 1)]
theorem atom1718Coded_decode : atom1718 = SparsePolynomial.decodeCubic 21 atom1718Coded := by decide +kernel
theorem atom1718Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34410212121600 : Int) atom1718Coded) := by
  have h := atom1718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1719 : SparsePolynomial.Poly := [([15,15,19], 1)]
theorem eval_atom1719 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1719 = ((g 15) * (g 15) * (g 19)) := by
  norm_num [atom1719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1719_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22182428620800 : Int) atom1719) := by
  rw [SparsePolynomial.eval_scale, eval_atom1719]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1719Coded : CoefficientMerge.Poly := [(6949, 1)]
theorem atom1719Coded_decode : atom1719 = SparsePolynomial.decodeCubic 21 atom1719Coded := by decide +kernel
theorem atom1719Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22182428620800 : Int) atom1719Coded) := by
  have h := atom1719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1720 : SparsePolynomial.Poly := [([15,15,20], 1)]
theorem eval_atom1720 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1720 = ((g 15) * (g 15) * (g 20)) := by
  norm_num [atom1720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1720_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44051720832000 : Int) atom1720) := by
  rw [SparsePolynomial.eval_scale, eval_atom1720]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1720Coded : CoefficientMerge.Poly := [(6950, 1)]
theorem atom1720Coded_decode : atom1720 = SparsePolynomial.decodeCubic 21 atom1720Coded := by decide +kernel
theorem atom1720Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44051720832000 : Int) atom1720Coded) := by
  have h := atom1720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1721 : SparsePolynomial.Poly := [([15,16,16], 1)]
theorem eval_atom1721 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1721 = ((g 15) * (g 16) * (g 16)) := by
  norm_num [atom1721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1721_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7849286000640 : Int) atom1721) := by
  rw [SparsePolynomial.eval_scale, eval_atom1721]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1721Coded : CoefficientMerge.Poly := [(6967, 1)]
theorem atom1721Coded_decode : atom1721 = SparsePolynomial.decodeCubic 21 atom1721Coded := by decide +kernel
theorem atom1721Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7849286000640 : Int) atom1721Coded) := by
  have h := atom1721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1722 : SparsePolynomial.Poly := [([15,16,17], 1)]
theorem eval_atom1722 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1722 = ((g 15) * (g 16) * (g 17)) := by
  norm_num [atom1722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1722_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56289827059200 : Int) atom1722) := by
  rw [SparsePolynomial.eval_scale, eval_atom1722]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1722Coded : CoefficientMerge.Poly := [(6968, 1)]
theorem atom1722Coded_decode : atom1722 = SparsePolynomial.decodeCubic 21 atom1722Coded := by decide +kernel
theorem atom1722Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56289827059200 : Int) atom1722Coded) := by
  have h := atom1722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1723 : SparsePolynomial.Poly := [([15,16,18], 1)]
theorem eval_atom1723 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1723 = ((g 15) * (g 16) * (g 18)) := by
  norm_num [atom1723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1723_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78697751731200 : Int) atom1723) := by
  rw [SparsePolynomial.eval_scale, eval_atom1723]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1723Coded : CoefficientMerge.Poly := [(6969, 1)]
theorem atom1723Coded_decode : atom1723 = SparsePolynomial.decodeCubic 21 atom1723Coded := by decide +kernel
theorem atom1723Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (78697751731200 : Int) atom1723Coded) := by
  have h := atom1723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1724 : SparsePolynomial.Poly := [([15,16,19], 1)]
theorem eval_atom1724 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1724 = ((g 15) * (g 16) * (g 19)) := by
  norm_num [atom1724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1724_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65457107251200 : Int) atom1724) := by
  rw [SparsePolynomial.eval_scale, eval_atom1724]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1724Coded : CoefficientMerge.Poly := [(6970, 1)]
theorem atom1724Coded_decode : atom1724 = SparsePolynomial.decodeCubic 21 atom1724Coded := by decide +kernel
theorem atom1724Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65457107251200 : Int) atom1724Coded) := by
  have h := atom1724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1725 : SparsePolynomial.Poly := [([15,16,20], 1)]
theorem eval_atom1725 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1725 = ((g 15) * (g 16) * (g 20)) := by
  norm_num [atom1725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1725_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94837807411200 : Int) atom1725) := by
  rw [SparsePolynomial.eval_scale, eval_atom1725]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1725Coded : CoefficientMerge.Poly := [(6971, 1)]
theorem atom1725Coded_decode : atom1725 = SparsePolynomial.decodeCubic 21 atom1725Coded := by decide +kernel
theorem atom1725Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (94837807411200 : Int) atom1725Coded) := by
  have h := atom1725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1726 : SparsePolynomial.Poly := [([15,17,17], 1)]
theorem eval_atom1726 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1726 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom1726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1726_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43748907148800 : Int) atom1726) := by
  rw [SparsePolynomial.eval_scale, eval_atom1726]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1726Coded : CoefficientMerge.Poly := [(6989, 1)]
theorem atom1726Coded_decode : atom1726 = SparsePolynomial.decodeCubic 21 atom1726Coded := by decide +kernel
theorem atom1726Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43748907148800 : Int) atom1726Coded) := by
  have h := atom1726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1727 : SparsePolynomial.Poly := [([15,17,18], 1)]
theorem eval_atom1727 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1727 = ((g 15) * (g 17) * (g 18)) := by
  norm_num [atom1727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1727_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95547854707200 : Int) atom1727) := by
  rw [SparsePolynomial.eval_scale, eval_atom1727]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1727Coded : CoefficientMerge.Poly := [(6990, 1)]
theorem atom1727Coded_decode : atom1727 = SparsePolynomial.decodeCubic 21 atom1727Coded := by decide +kernel
theorem atom1727Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (95547854707200 : Int) atom1727Coded) := by
  have h := atom1727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1728 : SparsePolynomial.Poly := [([15,17,19], 1)]
theorem eval_atom1728 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1728 = ((g 15) * (g 17) * (g 19)) := by
  norm_num [atom1728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1728_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85515028300800 : Int) atom1728) := by
  rw [SparsePolynomial.eval_scale, eval_atom1728]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1728Coded : CoefficientMerge.Poly := [(6991, 1)]
theorem atom1728Coded_decode : atom1728 = SparsePolynomial.decodeCubic 21 atom1728Coded := by decide +kernel
theorem atom1728Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (85515028300800 : Int) atom1728Coded) := by
  have h := atom1728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1729 : SparsePolynomial.Poly := [([15,17,20], 1)]
theorem eval_atom1729 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1729 = ((g 15) * (g 17) * (g 20)) := by
  norm_num [atom1729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1729_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85557964262400 : Int) atom1729) := by
  rw [SparsePolynomial.eval_scale, eval_atom1729]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1729Coded : CoefficientMerge.Poly := [(6992, 1)]
theorem atom1729Coded_decode : atom1729 = SparsePolynomial.decodeCubic 21 atom1729Coded := by decide +kernel
theorem atom1729Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (85557964262400 : Int) atom1729Coded) := by
  have h := atom1729_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1729Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1730 : SparsePolynomial.Poly := [([15,18,18], 1)]
theorem eval_atom1730 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1730 = ((g 15) * (g 18) * (g 18)) := by
  norm_num [atom1730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1730_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44964068889600 : Int) atom1730) := by
  rw [SparsePolynomial.eval_scale, eval_atom1730]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1730Coded : CoefficientMerge.Poly := [(7011, 1)]
theorem atom1730Coded_decode : atom1730 = SparsePolynomial.decodeCubic 21 atom1730Coded := by decide +kernel
theorem atom1730Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44964068889600 : Int) atom1730Coded) := by
  have h := atom1730_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1730Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1731 : SparsePolynomial.Poly := [([15,18,19], 1)]
theorem eval_atom1731 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1731 = ((g 15) * (g 18) * (g 19)) := by
  norm_num [atom1731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1731_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90593069414400 : Int) atom1731) := by
  rw [SparsePolynomial.eval_scale, eval_atom1731]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1731Coded : CoefficientMerge.Poly := [(7012, 1)]
theorem atom1731Coded_decode : atom1731 = SparsePolynomial.decodeCubic 21 atom1731Coded := by decide +kernel
theorem atom1731Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (90593069414400 : Int) atom1731Coded) := by
  have h := atom1731_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1731Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1732 : SparsePolynomial.Poly := [([15,18,20], 1)]
theorem eval_atom1732 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1732 = ((g 15) * (g 18) * (g 20)) := by
  norm_num [atom1732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1732_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91258001049600 : Int) atom1732) := by
  rw [SparsePolynomial.eval_scale, eval_atom1732]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1732Coded : CoefficientMerge.Poly := [(7013, 1)]
theorem atom1732Coded_decode : atom1732 = SparsePolynomial.decodeCubic 21 atom1732Coded := by decide +kernel
theorem atom1732Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (91258001049600 : Int) atom1732Coded) := by
  have h := atom1732_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1732Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1733 : SparsePolynomial.Poly := [([15,19,19], 1)]
theorem eval_atom1733 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1733 = ((g 15) * (g 19) * (g 19)) := by
  norm_num [atom1733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1733_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47318390784000 : Int) atom1733) := by
  rw [SparsePolynomial.eval_scale, eval_atom1733]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1733Coded : CoefficientMerge.Poly := [(7033, 1)]
theorem atom1733Coded_decode : atom1733 = SparsePolynomial.decodeCubic 21 atom1733Coded := by decide +kernel
theorem atom1733Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47318390784000 : Int) atom1733Coded) := by
  have h := atom1733_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1733Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1734 : SparsePolynomial.Poly := [([15,19,20], 1)]
theorem eval_atom1734 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1734 = ((g 15) * (g 19) * (g 20)) := by
  norm_num [atom1734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1734_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (97992366796800 : Int) atom1734) := by
  rw [SparsePolynomial.eval_scale, eval_atom1734]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1734Coded : CoefficientMerge.Poly := [(7034, 1)]
theorem atom1734Coded_decode : atom1734 = SparsePolynomial.decodeCubic 21 atom1734Coded := by decide +kernel
theorem atom1734Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (97992366796800 : Int) atom1734Coded) := by
  have h := atom1734_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1734Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1735 : SparsePolynomial.Poly := [([15,20,20], 1)]
theorem eval_atom1735 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1735 = ((g 15) * (g 20) * (g 20)) := by
  norm_num [atom1735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1735_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43839097344000 : Int) atom1735) := by
  rw [SparsePolynomial.eval_scale, eval_atom1735]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1735Coded : CoefficientMerge.Poly := [(7055, 1)]
theorem atom1735Coded_decode : atom1735 = SparsePolynomial.decodeCubic 21 atom1735Coded := by decide +kernel
theorem atom1735Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43839097344000 : Int) atom1735Coded) := by
  have h := atom1735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1736 : SparsePolynomial.Poly := [([16,16,17], 1)]
theorem eval_atom1736 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1736 = ((g 16) * (g 16) * (g 17)) := by
  norm_num [atom1736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1736_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19329111889920 : Int) atom1736) := by
  rw [SparsePolynomial.eval_scale, eval_atom1736]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1736Coded : CoefficientMerge.Poly := [(7409, 1)]
theorem atom1736Coded_decode : atom1736 = SparsePolynomial.decodeCubic 21 atom1736Coded := by decide +kernel
theorem atom1736Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19329111889920 : Int) atom1736Coded) := by
  have h := atom1736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1737 : SparsePolynomial.Poly := [([16,16,18], 1)]
theorem eval_atom1737 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1737 = ((g 16) * (g 16) * (g 18)) := by
  norm_num [atom1737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1737_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34842417684480 : Int) atom1737) := by
  rw [SparsePolynomial.eval_scale, eval_atom1737]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1737Coded : CoefficientMerge.Poly := [(7410, 1)]
theorem atom1737Coded_decode : atom1737 = SparsePolynomial.decodeCubic 21 atom1737Coded := by decide +kernel
theorem atom1737Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34842417684480 : Int) atom1737Coded) := by
  have h := atom1737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1738 : SparsePolynomial.Poly := [([16,16,19], 1)]
theorem eval_atom1738 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1738 = ((g 16) * (g 16) * (g 19)) := by
  norm_num [atom1738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1738_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32177665497600 : Int) atom1738) := by
  rw [SparsePolynomial.eval_scale, eval_atom1738]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1738Coded : CoefficientMerge.Poly := [(7411, 1)]
theorem atom1738Coded_decode : atom1738 = SparsePolynomial.decodeCubic 21 atom1738Coded := by decide +kernel
theorem atom1738Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32177665497600 : Int) atom1738Coded) := by
  have h := atom1738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1739 : SparsePolynomial.Poly := [([16,16,20], 1)]
theorem eval_atom1739 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1739 = ((g 16) * (g 16) * (g 20)) := by
  norm_num [atom1739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1739_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46561451166720 : Int) atom1739) := by
  rw [SparsePolynomial.eval_scale, eval_atom1739]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1739Coded : CoefficientMerge.Poly := [(7412, 1)]
theorem atom1739Coded_decode : atom1739 = SparsePolynomial.decodeCubic 21 atom1739Coded := by decide +kernel
theorem atom1739Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46561451166720 : Int) atom1739Coded) := by
  have h := atom1739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1740 : SparsePolynomial.Poly := [([16,17,17], 1)]
theorem eval_atom1740 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1740 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom1740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1740_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35376476889600 : Int) atom1740) := by
  rw [SparsePolynomial.eval_scale, eval_atom1740]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1740Coded : CoefficientMerge.Poly := [(7430, 1)]
theorem atom1740Coded_decode : atom1740 = SparsePolynomial.decodeCubic 21 atom1740Coded := by decide +kernel
theorem atom1740Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35376476889600 : Int) atom1740Coded) := by
  have h := atom1740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1741 : SparsePolynomial.Poly := [([16,17,18], 1)]
theorem eval_atom1741 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1741 = ((g 16) * (g 17) * (g 18)) := by
  norm_num [atom1741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1741_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88814558246400 : Int) atom1741) := by
  rw [SparsePolynomial.eval_scale, eval_atom1741]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1741Coded : CoefficientMerge.Poly := [(7431, 1)]
theorem atom1741Coded_decode : atom1741 = SparsePolynomial.decodeCubic 21 atom1741Coded := by decide +kernel
theorem atom1741Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (88814558246400 : Int) atom1741Coded) := by
  have h := atom1741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1742 : SparsePolynomial.Poly := [([16,17,19], 1)]
theorem eval_atom1742 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1742 = ((g 16) * (g 17) * (g 19)) := by
  norm_num [atom1742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1742_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88793295897600 : Int) atom1742) := by
  rw [SparsePolynomial.eval_scale, eval_atom1742]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1742Coded : CoefficientMerge.Poly := [(7432, 1)]
theorem atom1742Coded_decode : atom1742 = SparsePolynomial.decodeCubic 21 atom1742Coded := by decide +kernel
theorem atom1742Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (88793295897600 : Int) atom1742Coded) := by
  have h := atom1742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1743 : SparsePolynomial.Poly := [([16,17,20], 1)]
theorem eval_atom1743 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1743 = ((g 16) * (g 17) * (g 20)) := by
  norm_num [atom1743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1743_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90840691468800 : Int) atom1743) := by
  rw [SparsePolynomial.eval_scale, eval_atom1743]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1743Coded : CoefficientMerge.Poly := [(7433, 1)]
theorem atom1743Coded_decode : atom1743 = SparsePolynomial.decodeCubic 21 atom1743Coded := by decide +kernel
theorem atom1743Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (90840691468800 : Int) atom1743Coded) := by
  have h := atom1743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1744 : SparsePolynomial.Poly := [([16,18,18], 1)]
theorem eval_atom1744 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1744 = ((g 16) * (g 18) * (g 18)) := by
  norm_num [atom1744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1744_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46176022771200 : Int) atom1744) := by
  rw [SparsePolynomial.eval_scale, eval_atom1744]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1744Coded : CoefficientMerge.Poly := [(7452, 1)]
theorem atom1744Coded_decode : atom1744 = SparsePolynomial.decodeCubic 21 atom1744Coded := by decide +kernel
theorem atom1744Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46176022771200 : Int) atom1744Coded) := by
  have h := atom1744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1745 : SparsePolynomial.Poly := [([16,18,19], 1)]
theorem eval_atom1745 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1745 = ((g 16) * (g 18) * (g 19)) := by
  norm_num [atom1745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1745_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95189602636800 : Int) atom1745) := by
  rw [SparsePolynomial.eval_scale, eval_atom1745]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1745Coded : CoefficientMerge.Poly := [(7453, 1)]
theorem atom1745Coded_decode : atom1745 = SparsePolynomial.decodeCubic 21 atom1745Coded := by decide +kernel
theorem atom1745Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (95189602636800 : Int) atom1745Coded) := by
  have h := atom1745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1746 : SparsePolynomial.Poly := [([16,18,20], 1)]
theorem eval_atom1746 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1746 = ((g 16) * (g 18) * (g 20)) := by
  norm_num [atom1746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1746_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98027159731200 : Int) atom1746) := by
  rw [SparsePolynomial.eval_scale, eval_atom1746]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1746Coded : CoefficientMerge.Poly := [(7454, 1)]
theorem atom1746Coded_decode : atom1746 = SparsePolynomial.decodeCubic 21 atom1746Coded := by decide +kernel
theorem atom1746Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (98027159731200 : Int) atom1746Coded) := by
  have h := atom1746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1747 : SparsePolynomial.Poly := [([16,19,19], 1)]
theorem eval_atom1747 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1747 = ((g 16) * (g 19) * (g 19)) := by
  norm_num [atom1747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1747_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50275790208000 : Int) atom1747) := by
  rw [SparsePolynomial.eval_scale, eval_atom1747]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1747Coded : CoefficientMerge.Poly := [(7474, 1)]
theorem atom1747Coded_decode : atom1747 = SparsePolynomial.decodeCubic 21 atom1747Coded := by decide +kernel
theorem atom1747Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50275790208000 : Int) atom1747Coded) := by
  have h := atom1747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1748 : SparsePolynomial.Poly := [([16,19,20], 1)]
theorem eval_atom1748 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1748 = ((g 16) * (g 19) * (g 20)) := by
  norm_num [atom1748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1748_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106247956953600 : Int) atom1748) := by
  rw [SparsePolynomial.eval_scale, eval_atom1748]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1748Coded : CoefficientMerge.Poly := [(7475, 1)]
theorem atom1748Coded_decode : atom1748 = SparsePolynomial.decodeCubic 21 atom1748Coded := by decide +kernel
theorem atom1748Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (106247956953600 : Int) atom1748Coded) := by
  have h := atom1748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1749 : SparsePolynomial.Poly := [([16,20,20], 1)]
theorem eval_atom1749 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1749 = ((g 16) * (g 20) * (g 20)) := by
  norm_num [atom1749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1749_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48710108160000 : Int) atom1749) := by
  rw [SparsePolynomial.eval_scale, eval_atom1749]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1749Coded : CoefficientMerge.Poly := [(7496, 1)]
theorem atom1749Coded_decode : atom1749 = SparsePolynomial.decodeCubic 21 atom1749Coded := by decide +kernel
theorem atom1749Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48710108160000 : Int) atom1749Coded) := by
  have h := atom1749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1750 : SparsePolynomial.Poly := [([17,17,17], 1)]
theorem eval_atom1750 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1750 = ((g 17) * (g 17) * (g 17)) := by
  norm_num [atom1750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1750_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14339418508800 : Int) atom1750) := by
  rw [SparsePolynomial.eval_scale, eval_atom1750]
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 17) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1750Coded : CoefficientMerge.Poly := [(7871, 1)]
theorem atom1750Coded_decode : atom1750 = SparsePolynomial.decodeCubic 21 atom1750Coded := by decide +kernel
theorem atom1750Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14339418508800 : Int) atom1750Coded) := by
  have h := atom1750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1751 : SparsePolynomial.Poly := [([17,17,18], 1)]
theorem eval_atom1751 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1751 = ((g 17) * (g 17) * (g 18)) := by
  norm_num [atom1751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1751_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45044183116800 : Int) atom1751) := by
  rw [SparsePolynomial.eval_scale, eval_atom1751]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1751Coded : CoefficientMerge.Poly := [(7872, 1)]
theorem atom1751Coded_decode : atom1751 = SparsePolynomial.decodeCubic 21 atom1751Coded := by decide +kernel
theorem atom1751Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45044183116800 : Int) atom1751Coded) := by
  have h := atom1751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1752 : SparsePolynomial.Poly := [([17,17,19], 1)]
theorem eval_atom1752 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1752 = ((g 17) * (g 17) * (g 19)) := by
  norm_num [atom1752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1752_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46035781747200 : Int) atom1752) := by
  rw [SparsePolynomial.eval_scale, eval_atom1752]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1752Coded : CoefficientMerge.Poly := [(7873, 1)]
theorem atom1752Coded_decode : atom1752 = SparsePolynomial.decodeCubic 21 atom1752Coded := by decide +kernel
theorem atom1752Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46035781747200 : Int) atom1752Coded) := by
  have h := atom1752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1753 : SparsePolynomial.Poly := [([17,17,20], 1)]
theorem eval_atom1753 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1753 = ((g 17) * (g 17) * (g 20)) := by
  norm_num [atom1753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1753_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32047500441600 : Int) atom1753) := by
  rw [SparsePolynomial.eval_scale, eval_atom1753]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1753Coded : CoefficientMerge.Poly := [(7874, 1)]
theorem atom1753Coded_decode : atom1753 = SparsePolynomial.decodeCubic 21 atom1753Coded := by decide +kernel
theorem atom1753Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32047500441600 : Int) atom1753Coded) := by
  have h := atom1753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1754 : SparsePolynomial.Poly := [([17,18,18], 1)]
theorem eval_atom1754 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1754 = ((g 17) * (g 18) * (g 18)) := by
  norm_num [atom1754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1754_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47387976652800 : Int) atom1754) := by
  rw [SparsePolynomial.eval_scale, eval_atom1754]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1754Coded : CoefficientMerge.Poly := [(7893, 1)]
theorem atom1754Coded_decode : atom1754 = SparsePolynomial.decodeCubic 21 atom1754Coded := by decide +kernel
theorem atom1754Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47387976652800 : Int) atom1754Coded) := by
  have h := atom1754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1755 : SparsePolynomial.Poly := [([17,18,19], 1)]
theorem eval_atom1755 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1755 = ((g 17) * (g 18) * (g 19)) := by
  norm_num [atom1755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1755_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99786135859200 : Int) atom1755) := by
  rw [SparsePolynomial.eval_scale, eval_atom1755]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1755Coded : CoefficientMerge.Poly := [(7894, 1)]
theorem atom1755Coded_decode : atom1755 = SparsePolynomial.decodeCubic 21 atom1755Coded := by decide +kernel
theorem atom1755Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (99786135859200 : Int) atom1755Coded) := by
  have h := atom1755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1756 : SparsePolynomial.Poly := [([17,18,20], 1)]
theorem eval_atom1756 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1756 = ((g 17) * (g 18) * (g 20)) := by
  norm_num [atom1756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1756_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72767900620800 : Int) atom1756) := by
  rw [SparsePolynomial.eval_scale, eval_atom1756]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1756Coded : CoefficientMerge.Poly := [(7895, 1)]
theorem atom1756Coded_decode : atom1756 = SparsePolynomial.decodeCubic 21 atom1756Coded := by decide +kernel
theorem atom1756Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (72767900620800 : Int) atom1756Coded) := by
  have h := atom1756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1757 : SparsePolynomial.Poly := [([17,19,19], 1)]
theorem eval_atom1757 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1757 = ((g 17) * (g 19) * (g 19)) := by
  norm_num [atom1757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1757_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53233189632000 : Int) atom1757) := by
  rw [SparsePolynomial.eval_scale, eval_atom1757]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1757Coded : CoefficientMerge.Poly := [(7915, 1)]
theorem atom1757Coded_decode : atom1757 = SparsePolynomial.decodeCubic 21 atom1757Coded := by decide +kernel
theorem atom1757Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53233189632000 : Int) atom1757Coded) := by
  have h := atom1757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1758 : SparsePolynomial.Poly := [([17,19,20], 1)]
theorem eval_atom1758 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1758 = ((g 17) * (g 19) * (g 20)) := by
  norm_num [atom1758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1758_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82475129318400 : Int) atom1758) := by
  rw [SparsePolynomial.eval_scale, eval_atom1758]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1758Coded : CoefficientMerge.Poly := [(7916, 1)]
theorem atom1758Coded_decode : atom1758 = SparsePolynomial.decodeCubic 21 atom1758Coded := by decide +kernel
theorem atom1758Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82475129318400 : Int) atom1758Coded) := by
  have h := atom1758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1759 : SparsePolynomial.Poly := [([17,20,20], 1)]
theorem eval_atom1759 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1759 = ((g 17) * (g 20) * (g 20)) := by
  norm_num [atom1759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1759_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21552701184000 : Int) atom1759) := by
  rw [SparsePolynomial.eval_scale, eval_atom1759]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1759Coded : CoefficientMerge.Poly := [(7937, 1)]
theorem atom1759Coded_decode : atom1759 = SparsePolynomial.decodeCubic 21 atom1759Coded := by decide +kernel
theorem atom1759Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21552701184000 : Int) atom1759Coded) := by
  have h := atom1759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1760 : SparsePolynomial.Poly := [([18,18,18], 1)]
theorem eval_atom1760 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1760 = ((g 18) * (g 18) * (g 18)) := by
  norm_num [atom1760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1760_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16199976844800 : Int) atom1760) := by
  rw [SparsePolynomial.eval_scale, eval_atom1760]
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 18) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1760Coded : CoefficientMerge.Poly := [(8334, 1)]
theorem atom1760Coded_decode : atom1760 = SparsePolynomial.decodeCubic 21 atom1760Coded := by decide +kernel
theorem atom1760Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16199976844800 : Int) atom1760Coded) := by
  have h := atom1760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1761 : SparsePolynomial.Poly := [([18,18,19], 1)]
theorem eval_atom1761 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1761 = ((g 18) * (g 18) * (g 19)) := by
  norm_num [atom1761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1761_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52191334540800 : Int) atom1761) := by
  rw [SparsePolynomial.eval_scale, eval_atom1761]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1761Coded : CoefficientMerge.Poly := [(8335, 1)]
theorem atom1761Coded_decode : atom1761 = SparsePolynomial.decodeCubic 21 atom1761Coded := by decide +kernel
theorem atom1761Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52191334540800 : Int) atom1761Coded) := by
  have h := atom1761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1762 : SparsePolynomial.Poly := [([18,18,20], 1)]
theorem eval_atom1762 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1762 = ((g 18) * (g 18) * (g 20)) := by
  norm_num [atom1762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1762_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38734200691200 : Int) atom1762) := by
  rw [SparsePolynomial.eval_scale, eval_atom1762]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1762Coded : CoefficientMerge.Poly := [(8336, 1)]
theorem atom1762Coded_decode : atom1762 = SparsePolynomial.decodeCubic 21 atom1762Coded := by decide +kernel
theorem atom1762Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38734200691200 : Int) atom1762Coded) := by
  have h := atom1762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1763 : SparsePolynomial.Poly := [([18,19,19], 1)]
theorem eval_atom1763 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1763 = ((g 18) * (g 19) * (g 19)) := by
  norm_num [atom1763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1763_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56190589056000 : Int) atom1763) := by
  rw [SparsePolynomial.eval_scale, eval_atom1763]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 18) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1763Coded : CoefficientMerge.Poly := [(8356, 1)]
theorem atom1763Coded_decode : atom1763 = SparsePolynomial.decodeCubic 21 atom1763Coded := by decide +kernel
theorem atom1763Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56190589056000 : Int) atom1763Coded) := by
  have h := atom1763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1764 : SparsePolynomial.Poly := [([18,19,20], 1)]
theorem eval_atom1764 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1764 = ((g 18) * (g 19) * (g 20)) := by
  norm_num [atom1764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1764_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88662061555200 : Int) atom1764) := by
  rw [SparsePolynomial.eval_scale, eval_atom1764]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1764Coded : CoefficientMerge.Poly := [(8357, 1)]
theorem atom1764Coded_decode : atom1764 = SparsePolynomial.decodeCubic 21 atom1764Coded := by decide +kernel
theorem atom1764Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (88662061555200 : Int) atom1764Coded) := by
  have h := atom1764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1765 : SparsePolynomial.Poly := [([18,20,20], 1)]
theorem eval_atom1765 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1765 = ((g 18) * (g 20) * (g 20)) := by
  norm_num [atom1765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1765_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24355054080000 : Int) atom1765) := by
  rw [SparsePolynomial.eval_scale, eval_atom1765]
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 18) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1765Coded : CoefficientMerge.Poly := [(8378, 1)]
theorem atom1765Coded_decode : atom1765 = SparsePolynomial.decodeCubic 21 atom1765Coded := by decide +kernel
theorem atom1765Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24355054080000 : Int) atom1765Coded) := by
  have h := atom1765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1766 : SparsePolynomial.Poly := [([19,19,19], 1)]
theorem eval_atom1766 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1766 = ((g 19) * (g 19) * (g 19)) := by
  norm_num [atom1766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1766_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19715996160000 : Int) atom1766) := by
  rw [SparsePolynomial.eval_scale, eval_atom1766]
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 19) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1766Coded : CoefficientMerge.Poly := [(8797, 1)]
theorem atom1766Coded_decode : atom1766 = SparsePolynomial.decodeCubic 21 atom1766Coded := by decide +kernel
theorem atom1766Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19715996160000 : Int) atom1766Coded) := by
  have h := atom1766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1767 : SparsePolynomial.Poly := [([19,19,20], 1)]
theorem eval_atom1767 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1767 = ((g 19) * (g 19) * (g 20)) := by
  norm_num [atom1767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1767_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48458825856000 : Int) atom1767) := by
  rw [SparsePolynomial.eval_scale, eval_atom1767]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1767Coded : CoefficientMerge.Poly := [(8798, 1)]
theorem atom1767Coded_decode : atom1767 = SparsePolynomial.decodeCubic 21 atom1767Coded := by decide +kernel
theorem atom1767Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48458825856000 : Int) atom1767Coded) := by
  have h := atom1767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1768 : SparsePolynomial.Poly := [([19,20,20], 1)]
theorem eval_atom1768 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1768 = ((g 19) * (g 20) * (g 20)) := by
  norm_num [atom1768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1768_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29226064896000 : Int) atom1768) := by
  rw [SparsePolynomial.eval_scale, eval_atom1768]
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 19) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1768Coded : CoefficientMerge.Poly := [(8819, 1)]
theorem atom1768Coded_decode : atom1768 = SparsePolynomial.decodeCubic 21 atom1768Coded := by decide +kernel
theorem atom1768Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29226064896000 : Int) atom1768Coded) := by
  have h := atom1768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block023 : CoefficientMerge.Poly := [(6506, 49533129676800), (6507, 59532643699200), (6508, 43553022105600), (6509, 85602216268800), (6526, 4836604469760), (6527, 47815814592000), (6528, 68387445504000), (6529, 63497105280000), (6530, 91041511680000), (6548, 39020933952000), (6549, 84087448704000), (6550, 82236760704000), (6551, 98579775168000), (6570, 38658816000000), (6571, 85996536192000), (6572, 104862038400000), (6592, 44360991360000), (6593, 110109972672000), (6614, 59341282560000), (6945, 966470400000), (6946, 7720165555200), (6947, 28555128806400), (6948, 34410212121600), (6949, 22182428620800), (6950, 44051720832000), (6967, 7849286000640), (6968, 56289827059200), (6969, 78697751731200), (6970, 65457107251200), (6971, 94837807411200), (6989, 43748907148800), (6990, 95547854707200), (6991, 85515028300800), (6992, 85557964262400), (7011, 44964068889600), (7012, 90593069414400), (7013, 91258001049600), (7033, 47318390784000), (7034, 97992366796800), (7055, 43839097344000), (7409, 19329111889920), (7410, 34842417684480), (7411, 32177665497600), (7412, 46561451166720), (7430, 35376476889600), (7431, 88814558246400), (7432, 88793295897600), (7433, 90840691468800), (7452, 46176022771200), (7453, 95189602636800), (7454, 98027159731200), (7474, 50275790208000), (7475, 106247956953600), (7496, 48710108160000), (7871, 14339418508800), (7872, 45044183116800), (7873, 46035781747200), (7874, 32047500441600), (7893, 47387976652800), (7894, 99786135859200), (7895, 72767900620800), (7915, 53233189632000), (7916, 82475129318400), (7937, 21552701184000), (8334, 16199976844800), (8335, 52191334540800), (8336, 38734200691200), (8356, 56190589056000), (8357, 88662061555200), (8378, 24355054080000), (8797, 19715996160000), (8798, 48458825856000), (8819, 29226064896000)]
theorem block023_data : block023 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49533129676800 : Int) atom1696Coded) (CoefficientMerge.scale (59532643699200 : Int) atom1697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43553022105600 : Int) atom1698Coded) (CoefficientMerge.scale (85602216268800 : Int) atom1699Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4836604469760 : Int) atom1700Coded) (CoefficientMerge.scale (47815814592000 : Int) atom1701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68387445504000 : Int) atom1702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63497105280000 : Int) atom1703Coded) (CoefficientMerge.scale (91041511680000 : Int) atom1704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39020933952000 : Int) atom1705Coded) (CoefficientMerge.scale (84087448704000 : Int) atom1706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82236760704000 : Int) atom1707Coded) (CoefficientMerge.scale (98579775168000 : Int) atom1708Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38658816000000 : Int) atom1709Coded) (CoefficientMerge.scale (85996536192000 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104862038400000 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44360991360000 : Int) atom1712Coded) (CoefficientMerge.scale (110109972672000 : Int) atom1713Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59341282560000 : Int) atom1714Coded) (CoefficientMerge.scale (966470400000 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7720165555200 : Int) atom1716Coded) (CoefficientMerge.scale (28555128806400 : Int) atom1717Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34410212121600 : Int) atom1718Coded) (CoefficientMerge.scale (22182428620800 : Int) atom1719Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44051720832000 : Int) atom1720Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7849286000640 : Int) atom1721Coded) (CoefficientMerge.scale (56289827059200 : Int) atom1722Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78697751731200 : Int) atom1723Coded) (CoefficientMerge.scale (65457107251200 : Int) atom1724Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94837807411200 : Int) atom1725Coded) (CoefficientMerge.scale (43748907148800 : Int) atom1726Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95547854707200 : Int) atom1727Coded) (CoefficientMerge.scale (85515028300800 : Int) atom1728Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85557964262400 : Int) atom1729Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44964068889600 : Int) atom1730Coded) (CoefficientMerge.scale (90593069414400 : Int) atom1731Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91258001049600 : Int) atom1732Coded) (CoefficientMerge.scale (47318390784000 : Int) atom1733Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (97992366796800 : Int) atom1734Coded) (CoefficientMerge.scale (43839097344000 : Int) atom1735Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329111889920 : Int) atom1736Coded) (CoefficientMerge.scale (34842417684480 : Int) atom1737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32177665497600 : Int) atom1738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46561451166720 : Int) atom1739Coded) (CoefficientMerge.scale (35376476889600 : Int) atom1740Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88814558246400 : Int) atom1741Coded) (CoefficientMerge.scale (88793295897600 : Int) atom1742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90840691468800 : Int) atom1743Coded) (CoefficientMerge.scale (46176022771200 : Int) atom1744Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95189602636800 : Int) atom1745Coded) (CoefficientMerge.scale (98027159731200 : Int) atom1746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50275790208000 : Int) atom1747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106247956953600 : Int) atom1748Coded) (CoefficientMerge.scale (48710108160000 : Int) atom1749Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339418508800 : Int) atom1750Coded) (CoefficientMerge.scale (45044183116800 : Int) atom1751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46035781747200 : Int) atom1752Coded) (CoefficientMerge.scale (32047500441600 : Int) atom1753Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47387976652800 : Int) atom1754Coded) (CoefficientMerge.scale (99786135859200 : Int) atom1755Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (72767900620800 : Int) atom1756Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53233189632000 : Int) atom1757Coded) (CoefficientMerge.scale (82475129318400 : Int) atom1758Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21552701184000 : Int) atom1759Coded) (CoefficientMerge.scale (16199976844800 : Int) atom1760Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52191334540800 : Int) atom1761Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38734200691200 : Int) atom1762Coded) (CoefficientMerge.scale (56190589056000 : Int) atom1763Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88662061555200 : Int) atom1764Coded) (CoefficientMerge.scale (24355054080000 : Int) atom1765Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19715996160000 : Int) atom1766Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48458825856000 : Int) atom1767Coded) (CoefficientMerge.scale (29226064896000 : Int) atom1768Coded)))))))) := by decide +kernel
theorem block023_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block023 := by
  rw [block023_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1696Coded_nonneg g hg hA hB) (atom1697Coded_nonneg g hg hA hB)) (add_nonneg (atom1698Coded_nonneg g hg hA hB) (atom1699Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1700Coded_nonneg g hg hA hB) (atom1701Coded_nonneg g hg hA hB)) (add_nonneg (atom1702Coded_nonneg g hg hA hB) (add_nonneg (atom1703Coded_nonneg g hg hA hB) (atom1704Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1705Coded_nonneg g hg hA hB) (atom1706Coded_nonneg g hg hA hB)) (add_nonneg (atom1707Coded_nonneg g hg hA hB) (atom1708Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1709Coded_nonneg g hg hA hB) (atom1710Coded_nonneg g hg hA hB)) (add_nonneg (atom1711Coded_nonneg g hg hA hB) (add_nonneg (atom1712Coded_nonneg g hg hA hB) (atom1713Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1714Coded_nonneg g hg hA hB) (atom1715Coded_nonneg g hg hA hB)) (add_nonneg (atom1716Coded_nonneg g hg hA hB) (atom1717Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1718Coded_nonneg g hg hA hB) (atom1719Coded_nonneg g hg hA hB)) (add_nonneg (atom1720Coded_nonneg g hg hA hB) (add_nonneg (atom1721Coded_nonneg g hg hA hB) (atom1722Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1723Coded_nonneg g hg hA hB) (atom1724Coded_nonneg g hg hA hB)) (add_nonneg (atom1725Coded_nonneg g hg hA hB) (atom1726Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1727Coded_nonneg g hg hA hB) (atom1728Coded_nonneg g hg hA hB)) (add_nonneg (atom1729Coded_nonneg g hg hA hB) (add_nonneg (atom1730Coded_nonneg g hg hA hB) (atom1731Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1732Coded_nonneg g hg hA hB) (atom1733Coded_nonneg g hg hA hB)) (add_nonneg (atom1734Coded_nonneg g hg hA hB) (atom1735Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1736Coded_nonneg g hg hA hB) (atom1737Coded_nonneg g hg hA hB)) (add_nonneg (atom1738Coded_nonneg g hg hA hB) (add_nonneg (atom1739Coded_nonneg g hg hA hB) (atom1740Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1741Coded_nonneg g hg hA hB) (atom1742Coded_nonneg g hg hA hB)) (add_nonneg (atom1743Coded_nonneg g hg hA hB) (atom1744Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1745Coded_nonneg g hg hA hB) (atom1746Coded_nonneg g hg hA hB)) (add_nonneg (atom1747Coded_nonneg g hg hA hB) (add_nonneg (atom1748Coded_nonneg g hg hA hB) (atom1749Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1750Coded_nonneg g hg hA hB) (atom1751Coded_nonneg g hg hA hB)) (add_nonneg (atom1752Coded_nonneg g hg hA hB) (atom1753Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom1754Coded_nonneg g hg hA hB) (atom1755Coded_nonneg g hg hA hB)) (add_nonneg (atom1756Coded_nonneg g hg hA hB) (add_nonneg (atom1757Coded_nonneg g hg hA hB) (atom1758Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1759Coded_nonneg g hg hA hB) (atom1760Coded_nonneg g hg hA hB)) (add_nonneg (atom1761Coded_nonneg g hg hA hB) (add_nonneg (atom1762Coded_nonneg g hg hA hB) (atom1763Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1764Coded_nonneg g hg hA hB) (atom1765Coded_nonneg g hg hA hB)) (add_nonneg (atom1766Coded_nonneg g hg hA hB) (add_nonneg (atom1767Coded_nonneg g hg hA hB) (atom1768Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
