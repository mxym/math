-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0735 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0735Coded : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 1))]
theorem atom0735Coded_decode : atom0735 = SparsePolynomial.decodeCubic 18 atom0735Coded := by decide +kernel
theorem atom0735Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) := by
  have h := atom0735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0736 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0736 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4983552000 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736Coded : CoefficientMerge.Poly := [(nat_lit 1524, Int.ofNat (nat_lit 1))]
theorem atom0736Coded_decode : atom0736 = SparsePolynomial.decodeCubic 18 atom0736Coded := by decide +kernel
theorem atom0736Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded) := by
  have h := atom0736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0737 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0737Coded : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 1))]
theorem atom0737Coded_decode : atom0737 = SparsePolynomial.decodeCubic 18 atom0737Coded := by decide +kernel
theorem atom0737Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) := by
  have h := atom0737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0738 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0738Coded : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 1))]
theorem atom0738Coded_decode : atom0738 = SparsePolynomial.decodeCubic 18 atom0738Coded := by decide +kernel
theorem atom0738Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) := by
  have h := atom0738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0739 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0739Coded : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 1))]
theorem atom0739Coded_decode : atom0739 = SparsePolynomial.decodeCubic 18 atom0739Coded := by decide +kernel
theorem atom0739Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded) := by
  have h := atom0739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0740 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0740Coded : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 1))]
theorem atom0740Coded_decode : atom0740 = SparsePolynomial.decodeCubic 18 atom0740Coded := by decide +kernel
theorem atom0740Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) := by
  have h := atom0740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0741 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0741Coded : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 1))]
theorem atom0741Coded_decode : atom0741 = SparsePolynomial.decodeCubic 18 atom0741Coded := by decide +kernel
theorem atom0741Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded) := by
  have h := atom0741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0742 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0742 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3690344448 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742Coded : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 1))]
theorem atom0742Coded_decode : atom0742 = SparsePolynomial.decodeCubic 18 atom0742Coded := by decide +kernel
theorem atom0742Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) := by
  have h := atom0742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0743 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0743Coded : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 1))]
theorem atom0743Coded_decode : atom0743 = SparsePolynomial.decodeCubic 18 atom0743Coded := by decide +kernel
theorem atom0743Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) := by
  have h := atom0743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0744 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0744Coded : CoefficientMerge.Poly := [(nat_lit 1545, Int.ofNat (nat_lit 1))]
theorem atom0744Coded_decode : atom0744 = SparsePolynomial.decodeCubic 18 atom0744Coded := by decide +kernel
theorem atom0744Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded) := by
  have h := atom0744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0745 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0745Coded : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 1))]
theorem atom0745Coded_decode : atom0745 = SparsePolynomial.decodeCubic 18 atom0745Coded := by decide +kernel
theorem atom0745Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) := by
  have h := atom0745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0746 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0746Coded : CoefficientMerge.Poly := [(nat_lit 1547, Int.ofNat (nat_lit 1))]
theorem atom0746Coded_decode : atom0746 = SparsePolynomial.decodeCubic 18 atom0746Coded := by decide +kernel
theorem atom0746Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded) := by
  have h := atom0746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0747 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0747 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7996131000 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747Coded : CoefficientMerge.Poly := [(nat_lit 1562, Int.ofNat (nat_lit 1))]
theorem atom0747Coded_decode : atom0747 = SparsePolynomial.decodeCubic 18 atom0747Coded := by decide +kernel
theorem atom0747Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) := by
  have h := atom0747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0748 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0748Coded : CoefficientMerge.Poly := [(nat_lit 1563, Int.ofNat (nat_lit 1))]
theorem atom0748Coded_decode : atom0748 = SparsePolynomial.decodeCubic 18 atom0748Coded := by decide +kernel
theorem atom0748Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) := by
  have h := atom0748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0749 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0749Coded : CoefficientMerge.Poly := [(nat_lit 1564, Int.ofNat (nat_lit 1))]
theorem atom0749Coded_decode : atom0749 = SparsePolynomial.decodeCubic 18 atom0749Coded := by decide +kernel
theorem atom0749Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded) := by
  have h := atom0749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0750 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0750Coded : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 1))]
theorem atom0750Coded_decode : atom0750 = SparsePolynomial.decodeCubic 18 atom0750Coded := by decide +kernel
theorem atom0750Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) := by
  have h := atom0750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0751 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0751 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3641223600 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751Coded : CoefficientMerge.Poly := [(nat_lit 1581, Int.ofNat (nat_lit 1))]
theorem atom0751Coded_decode : atom0751 = SparsePolynomial.decodeCubic 18 atom0751Coded := by decide +kernel
theorem atom0751Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded) := by
  have h := atom0751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0752 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0752Coded : CoefficientMerge.Poly := [(nat_lit 1582, Int.ofNat (nat_lit 1))]
theorem atom0752Coded_decode : atom0752 = SparsePolynomial.decodeCubic 18 atom0752Coded := by decide +kernel
theorem atom0752Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) := by
  have h := atom0752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0753 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0753Coded : CoefficientMerge.Poly := [(nat_lit 1583, Int.ofNat (nat_lit 1))]
theorem atom0753Coded_decode : atom0753 = SparsePolynomial.decodeCubic 18 atom0753Coded := by decide +kernel
theorem atom0753Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) := by
  have h := atom0753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0754 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0754Coded : CoefficientMerge.Poly := [(nat_lit 1601, Int.ofNat (nat_lit 1))]
theorem atom0754Coded_decode : atom0754 = SparsePolynomial.decodeCubic 18 atom0754Coded := by decide +kernel
theorem atom0754Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded) := by
  have h := atom0754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0755 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0755 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2764487880 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755Coded : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 1))]
theorem atom0755Coded_decode : atom0755 = SparsePolynomial.decodeCubic 18 atom0755Coded := by decide +kernel
theorem atom0755Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) := by
  have h := atom0755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0756 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0756 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (580913280 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756Coded : CoefficientMerge.Poly := [(nat_lit 1715, Int.ofNat (nat_lit 1))]
theorem atom0756Coded_decode : atom0756 = SparsePolynomial.decodeCubic 18 atom0756Coded := by decide +kernel
theorem atom0756Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (580913280 : Int) atom0756Coded) := by
  have h := atom0756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0757 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0757 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (807960960 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757Coded : CoefficientMerge.Poly := [(nat_lit 1716, Int.ofNat (nat_lit 1))]
theorem atom0757Coded_decode : atom0757 = SparsePolynomial.decodeCubic 18 atom0757Coded := by decide +kernel
theorem atom0757Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (807960960 : Int) atom0757Coded) := by
  have h := atom0757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0758 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0758 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758Coded : CoefficientMerge.Poly := [(nat_lit 1717, Int.ofNat (nat_lit 1))]
theorem atom0758Coded_decode : atom0758 = SparsePolynomial.decodeCubic 18 atom0758Coded := by decide +kernel
theorem atom0758Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0758Coded) := by
  have h := atom0758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0759 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0759 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78704640 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759Coded : CoefficientMerge.Poly := [(nat_lit 1718, Int.ofNat (nat_lit 1))]
theorem atom0759Coded_decode : atom0759 = SparsePolynomial.decodeCubic 18 atom0759Coded := by decide +kernel
theorem atom0759Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (78704640 : Int) atom0759Coded) := by
  have h := atom0759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0760 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0760 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (960689520 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760Coded : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 1))]
theorem atom0760Coded_decode : atom0760 = SparsePolynomial.decodeCubic 18 atom0760Coded := by decide +kernel
theorem atom0760Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (960689520 : Int) atom0760Coded) := by
  have h := atom0760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0761 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0761 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761Coded : CoefficientMerge.Poly := [(nat_lit 1734, Int.ofNat (nat_lit 1))]
theorem atom0761Coded_decode : atom0761 = SparsePolynomial.decodeCubic 18 atom0761Coded := by decide +kernel
theorem atom0761Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (546687360 : Int) atom0761Coded) := by
  have h := atom0761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0762 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom0762Coded : CoefficientMerge.Poly := [(nat_lit 1738, Int.ofNat (nat_lit 1))]
theorem atom0762Coded_decode : atom0762 = SparsePolynomial.decodeCubic 18 atom0762Coded := by decide +kernel
theorem atom0762Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0762Coded) := by
  have h := atom0762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0763 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom0763Coded : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 1))]
theorem atom0763Coded_decode : atom0763 = SparsePolynomial.decodeCubic 18 atom0763Coded := by decide +kernel
theorem atom0763Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (207728640 : Int) atom0763Coded) := by
  have h := atom0763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0764 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0764Coded : CoefficientMerge.Poly := [(nat_lit 1740, Int.ofNat (nat_lit 1))]
theorem atom0764Coded_decode : atom0764 = SparsePolynomial.decodeCubic 18 atom0764Coded := by decide +kernel
theorem atom0764Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded) := by
  have h := atom0764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0765 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0765Coded : CoefficientMerge.Poly := [(nat_lit 1742, Int.ofNat (nat_lit 1))]
theorem atom0765Coded_decode : atom0765 = SparsePolynomial.decodeCubic 18 atom0765Coded := by decide +kernel
theorem atom0765Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (173304000 : Int) atom0765Coded) := by
  have h := atom0765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0766 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0766Coded : CoefficientMerge.Poly := [(nat_lit 1743, Int.ofNat (nat_lit 1))]
theorem atom0766Coded_decode : atom0766 = SparsePolynomial.decodeCubic 18 atom0766Coded := by decide +kernel
theorem atom0766Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded) := by
  have h := atom0766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0767 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0767Coded : CoefficientMerge.Poly := [(nat_lit 1744, Int.ofNat (nat_lit 1))]
theorem atom0767Coded_decode : atom0767 = SparsePolynomial.decodeCubic 18 atom0767Coded := by decide +kernel
theorem atom0767Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) := by
  have h := atom0767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0768 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0768Coded : CoefficientMerge.Poly := [(nat_lit 1745, Int.ofNat (nat_lit 1))]
theorem atom0768Coded_decode : atom0768 = SparsePolynomial.decodeCubic 18 atom0768Coded := by decide +kernel
theorem atom0768Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) := by
  have h := atom0768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0769 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0769 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126817920 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769Coded : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 1))]
theorem atom0769Coded_decode : atom0769 = SparsePolynomial.decodeCubic 18 atom0769Coded := by decide +kernel
theorem atom0769Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (126817920 : Int) atom0769Coded) := by
  have h := atom0769_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0769Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0770 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom0770Coded : CoefficientMerge.Poly := [(nat_lit 1756, Int.ofNat (nat_lit 1))]
theorem atom0770Coded_decode : atom0770 = SparsePolynomial.decodeCubic 18 atom0770Coded := by decide +kernel
theorem atom0770Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (157409280 : Int) atom0770Coded) := by
  have h := atom0770_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0770Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0771 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom0771Coded : CoefficientMerge.Poly := [(nat_lit 1757, Int.ofNat (nat_lit 1))]
theorem atom0771Coded_decode : atom0771 = SparsePolynomial.decodeCubic 18 atom0771Coded := by decide +kernel
theorem atom0771Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (314818560 : Int) atom0771Coded) := by
  have h := atom0771_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0771Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0772 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0772Coded : CoefficientMerge.Poly := [(nat_lit 1758, Int.ofNat (nat_lit 1))]
theorem atom0772Coded_decode : atom0772 = SparsePolynomial.decodeCubic 18 atom0772Coded := by decide +kernel
theorem atom0772Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) := by
  have h := atom0772_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0772Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0773 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0773Coded : CoefficientMerge.Poly := [(nat_lit 1759, Int.ofNat (nat_lit 1))]
theorem atom0773Coded_decode : atom0773 = SparsePolynomial.decodeCubic 18 atom0773Coded := by decide +kernel
theorem atom0773Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (748771920 : Int) atom0773Coded) := by
  have h := atom0773_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0773Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0774 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0774Coded : CoefficientMerge.Poly := [(nat_lit 1760, Int.ofNat (nat_lit 1))]
theorem atom0774Coded_decode : atom0774 = SparsePolynomial.decodeCubic 18 atom0774Coded := by decide +kernel
theorem atom0774Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded) := by
  have h := atom0774_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0774Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0775 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0775Coded : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 1))]
theorem atom0775Coded_decode : atom0775 = SparsePolynomial.decodeCubic 18 atom0775Coded := by decide +kernel
theorem atom0775Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) := by
  have h := atom0775_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0775Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0776 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0776Coded : CoefficientMerge.Poly := [(nat_lit 1762, Int.ofNat (nat_lit 1))]
theorem atom0776Coded_decode : atom0776 = SparsePolynomial.decodeCubic 18 atom0776Coded := by decide +kernel
theorem atom0776Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded) := by
  have h := atom0776_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0776Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0777 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0777Coded : CoefficientMerge.Poly := [(nat_lit 1763, Int.ofNat (nat_lit 1))]
theorem atom0777Coded_decode : atom0777 = SparsePolynomial.decodeCubic 18 atom0777Coded := by decide +kernel
theorem atom0777Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) := by
  have h := atom0777_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0777Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0778 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0778 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (546687360 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778Coded : CoefficientMerge.Poly := [(nat_lit 1772, Int.ofNat (nat_lit 1))]
theorem atom0778Coded_decode : atom0778 = SparsePolynomial.decodeCubic 18 atom0778Coded := by decide +kernel
theorem atom0778Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (546687360 : Int) atom0778Coded) := by
  have h := atom0778_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0778Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0779 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
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
def atom0779Coded : CoefficientMerge.Poly := [(nat_lit 1773, Int.ofNat (nat_lit 1))]
theorem atom0779Coded_decode : atom0779 = SparsePolynomial.decodeCubic 18 atom0779Coded := by decide +kernel
theorem atom0779Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (832953600 : Int) atom0779Coded) := by
  have h := atom0779_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0779Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0780 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom0780Coded : CoefficientMerge.Poly := [(nat_lit 1774, Int.ofNat (nat_lit 1))]
theorem atom0780Coded_decode : atom0780 = SparsePolynomial.decodeCubic 18 atom0780Coded := by decide +kernel
theorem atom0780Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (993588480 : Int) atom0780Coded) := by
  have h := atom0780_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0780Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0781 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom0781Coded : CoefficientMerge.Poly := [(nat_lit 1775, Int.ofNat (nat_lit 1))]
theorem atom0781Coded_decode : atom0781 = SparsePolynomial.decodeCubic 18 atom0781Coded := by decide +kernel
theorem atom0781Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded) := by
  have h := atom0781_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0781Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0782 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0782Coded : CoefficientMerge.Poly := [(nat_lit 1776, Int.ofNat (nat_lit 1))]
theorem atom0782Coded_decode : atom0782 = SparsePolynomial.decodeCubic 18 atom0782Coded := by decide +kernel
theorem atom0782Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) := by
  have h := atom0782_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0782Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0783 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0783Coded : CoefficientMerge.Poly := [(nat_lit 1777, Int.ofNat (nat_lit 1))]
theorem atom0783Coded_decode : atom0783 = SparsePolynomial.decodeCubic 18 atom0783Coded := by decide +kernel
theorem atom0783Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) := by
  have h := atom0783_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0783Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0784 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0784Coded : CoefficientMerge.Poly := [(nat_lit 1778, Int.ofNat (nat_lit 1))]
theorem atom0784Coded_decode : atom0784 = SparsePolynomial.decodeCubic 18 atom0784Coded := by decide +kernel
theorem atom0784Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded) := by
  have h := atom0784_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0784Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0785 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0785Coded : CoefficientMerge.Poly := [(nat_lit 1779, Int.ofNat (nat_lit 1))]
theorem atom0785Coded_decode : atom0785 = SparsePolynomial.decodeCubic 18 atom0785Coded := by decide +kernel
theorem atom0785Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) := by
  have h := atom0785_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0785Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0786 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0786Coded : CoefficientMerge.Poly := [(nat_lit 1780, Int.ofNat (nat_lit 1))]
theorem atom0786Coded_decode : atom0786 = SparsePolynomial.decodeCubic 18 atom0786Coded := by decide +kernel
theorem atom0786Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded) := by
  have h := atom0786_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0786Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0787 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0787Coded : CoefficientMerge.Poly := [(nat_lit 1781, Int.ofNat (nat_lit 1))]
theorem atom0787Coded_decode : atom0787 = SparsePolynomial.decodeCubic 18 atom0787Coded := by decide +kernel
theorem atom0787Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) := by
  have h := atom0787_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0787Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0788 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0788 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1063635840 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788Coded : CoefficientMerge.Poly := [(nat_lit 1791, Int.ofNat (nat_lit 1))]
theorem atom0788Coded_decode : atom0788 = SparsePolynomial.decodeCubic 18 atom0788Coded := by decide +kernel
theorem atom0788Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) := by
  have h := atom0788_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0788Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0789 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom0789Coded : CoefficientMerge.Poly := [(nat_lit 1792, Int.ofNat (nat_lit 1))]
theorem atom0789Coded_decode : atom0789 = SparsePolynomial.decodeCubic 18 atom0789Coded := by decide +kernel
theorem atom0789Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded) := by
  have h := atom0789_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0789Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0790 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom0790Coded : CoefficientMerge.Poly := [(nat_lit 1793, Int.ofNat (nat_lit 1))]
theorem atom0790Coded_decode : atom0790 = SparsePolynomial.decodeCubic 18 atom0790Coded := by decide +kernel
theorem atom0790Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) := by
  have h := atom0790_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0790Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0791 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0791Coded : CoefficientMerge.Poly := [(nat_lit 1794, Int.ofNat (nat_lit 1))]
theorem atom0791Coded_decode : atom0791 = SparsePolynomial.decodeCubic 18 atom0791Coded := by decide +kernel
theorem atom0791Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded) := by
  have h := atom0791_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0791Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0792 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0792Coded : CoefficientMerge.Poly := [(nat_lit 1795, Int.ofNat (nat_lit 1))]
theorem atom0792Coded_decode : atom0792 = SparsePolynomial.decodeCubic 18 atom0792Coded := by decide +kernel
theorem atom0792Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) := by
  have h := atom0792_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0792Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0793 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0793Coded : CoefficientMerge.Poly := [(nat_lit 1796, Int.ofNat (nat_lit 1))]
theorem atom0793Coded_decode : atom0793 = SparsePolynomial.decodeCubic 18 atom0793Coded := by decide +kernel
theorem atom0793Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) := by
  have h := atom0793_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0793Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0794 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0794Coded : CoefficientMerge.Poly := [(nat_lit 1797, Int.ofNat (nat_lit 1))]
theorem atom0794Coded_decode : atom0794 = SparsePolynomial.decodeCubic 18 atom0794Coded := by decide +kernel
theorem atom0794Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded) := by
  have h := atom0794_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0794Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0795 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0795Coded : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 1))]
theorem atom0795Coded_decode : atom0795 = SparsePolynomial.decodeCubic 18 atom0795Coded := by decide +kernel
theorem atom0795Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) := by
  have h := atom0795_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0795Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0796 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0796Coded : CoefficientMerge.Poly := [(nat_lit 1799, Int.ofNat (nat_lit 1))]
theorem atom0796Coded_decode : atom0796 = SparsePolynomial.decodeCubic 18 atom0796Coded := by decide +kernel
theorem atom0796Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded) := by
  have h := atom0796_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0796Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0797 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0797 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1707696000 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797Coded : CoefficientMerge.Poly := [(nat_lit 1810, Int.ofNat (nat_lit 1))]
theorem atom0797Coded_decode : atom0797 = SparsePolynomial.decodeCubic 18 atom0797Coded := by decide +kernel
theorem atom0797Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) := by
  have h := atom0797_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0797Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0798 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom0798Coded : CoefficientMerge.Poly := [(nat_lit 1811, Int.ofNat (nat_lit 1))]
theorem atom0798Coded_decode : atom0798 = SparsePolynomial.decodeCubic 18 atom0798Coded := by decide +kernel
theorem atom0798Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) := by
  have h := atom0798_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0798Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0799 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0799Coded : CoefficientMerge.Poly := [(nat_lit 1812, Int.ofNat (nat_lit 1))]
theorem atom0799Coded_decode : atom0799 = SparsePolynomial.decodeCubic 18 atom0799Coded := by decide +kernel
theorem atom0799Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded) := by
  have h := atom0799_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0799Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0800 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0800Coded : CoefficientMerge.Poly := [(nat_lit 1813, Int.ofNat (nat_lit 1))]
theorem atom0800Coded_decode : atom0800 = SparsePolynomial.decodeCubic 18 atom0800Coded := by decide +kernel
theorem atom0800Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) := by
  have h := atom0800_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0800Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0801 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0801Coded : CoefficientMerge.Poly := [(nat_lit 1814, Int.ofNat (nat_lit 1))]
theorem atom0801Coded_decode : atom0801 = SparsePolynomial.decodeCubic 18 atom0801Coded := by decide +kernel
theorem atom0801Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded) := by
  have h := atom0801_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0801Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0802 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0802Coded : CoefficientMerge.Poly := [(nat_lit 1815, Int.ofNat (nat_lit 1))]
theorem atom0802Coded_decode : atom0802 = SparsePolynomial.decodeCubic 18 atom0802Coded := by decide +kernel
theorem atom0802Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) := by
  have h := atom0802_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0802Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0803 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0803Coded : CoefficientMerge.Poly := [(nat_lit 1816, Int.ofNat (nat_lit 1))]
theorem atom0803Coded_decode : atom0803 = SparsePolynomial.decodeCubic 18 atom0803Coded := by decide +kernel
theorem atom0803Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) := by
  have h := atom0803_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0803Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0804 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0804Coded : CoefficientMerge.Poly := [(nat_lit 1817, Int.ofNat (nat_lit 1))]
theorem atom0804Coded_decode : atom0804 = SparsePolynomial.decodeCubic 18 atom0804Coded := by decide +kernel
theorem atom0804Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded) := by
  have h := atom0804_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0804Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0805 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0805 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2604689280 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805Coded : CoefficientMerge.Poly := [(nat_lit 1829, Int.ofNat (nat_lit 1))]
theorem atom0805Coded_decode : atom0805 = SparsePolynomial.decodeCubic 18 atom0805Coded := by decide +kernel
theorem atom0805Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) := by
  have h := atom0805_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0805Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0806 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom0806Coded : CoefficientMerge.Poly := [(nat_lit 1830, Int.ofNat (nat_lit 1))]
theorem atom0806Coded_decode : atom0806 = SparsePolynomial.decodeCubic 18 atom0806Coded := by decide +kernel
theorem atom0806Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded) := by
  have h := atom0806_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0806Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0807 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0807Coded : CoefficientMerge.Poly := [(nat_lit 1831, Int.ofNat (nat_lit 1))]
theorem atom0807Coded_decode : atom0807 = SparsePolynomial.decodeCubic 18 atom0807Coded := by decide +kernel
theorem atom0807Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) := by
  have h := atom0807_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0807Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0808 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0808Coded : CoefficientMerge.Poly := [(nat_lit 1832, Int.ofNat (nat_lit 1))]
theorem atom0808Coded_decode : atom0808 = SparsePolynomial.decodeCubic 18 atom0808Coded := by decide +kernel
theorem atom0808Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) := by
  have h := atom0808_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0808Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0809 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom0809Coded : CoefficientMerge.Poly := [(nat_lit 1833, Int.ofNat (nat_lit 1))]
theorem atom0809Coded_decode : atom0809 = SparsePolynomial.decodeCubic 18 atom0809Coded := by decide +kernel
theorem atom0809Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded) := by
  have h := atom0809_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0809Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0810 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom0810Coded : CoefficientMerge.Poly := [(nat_lit 1834, Int.ofNat (nat_lit 1))]
theorem atom0810Coded_decode : atom0810 = SparsePolynomial.decodeCubic 18 atom0810Coded := by decide +kernel
theorem atom0810Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) := by
  have h := atom0810_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0810Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0811 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom0811Coded : CoefficientMerge.Poly := [(nat_lit 1835, Int.ofNat (nat_lit 1))]
theorem atom0811Coded_decode : atom0811 = SparsePolynomial.decodeCubic 18 atom0811Coded := by decide +kernel
theorem atom0811Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded) := by
  have h := atom0811_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0811Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0812 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0812 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4203601920 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812Coded : CoefficientMerge.Poly := [(nat_lit 1848, Int.ofNat (nat_lit 1))]
theorem atom0812Coded_decode : atom0812 = SparsePolynomial.decodeCubic 18 atom0812Coded := by decide +kernel
theorem atom0812Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) := by
  have h := atom0812_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0812Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0813 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom0813Coded : CoefficientMerge.Poly := [(nat_lit 1849, Int.ofNat (nat_lit 1))]
theorem atom0813Coded_decode : atom0813 = SparsePolynomial.decodeCubic 18 atom0813Coded := by decide +kernel
theorem atom0813Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) := by
  have h := atom0813_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0813Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0814 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom0814Coded : CoefficientMerge.Poly := [(nat_lit 1850, Int.ofNat (nat_lit 1))]
theorem atom0814Coded_decode : atom0814 = SparsePolynomial.decodeCubic 18 atom0814Coded := by decide +kernel
theorem atom0814Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded) := by
  have h := atom0814_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0814Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block010 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840)), (nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440)), (nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792)), (nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240)), (nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920)), (nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520)), (nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480)), (nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
def block010_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520))]
theorem block010_data_flat000_step : block010_data_flat000 = (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) := by decide +kernel
theorem block010_data_flat000_original : block010_data_flat000 = (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) := by
  rw [block010_data_flat000_step]
def block010_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1524, Int.ofNat (nat_lit 4983552000))]
theorem block010_data_flat001_step : block010_data_flat001 = (CoefficientMerge.scale (4983552000 : Int) atom0736Coded) := by decide +kernel
theorem block010_data_flat001_original : block010_data_flat001 = (CoefficientMerge.scale (4983552000 : Int) atom0736Coded) := by
  rw [block010_data_flat001_step]
def block010_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000))]
theorem block010_data_flat002_step : block010_data_flat002 = (CoefficientMerge.fastMerge block010_data_flat000 block010_data_flat001) := by decide +kernel
theorem block010_data_flat002_original : block010_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) := by
  rw [block010_data_flat002_step, block010_data_flat000_original, block010_data_flat001_original]
def block010_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 8680213920))]
theorem block010_data_flat003_step : block010_data_flat003 = (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) := by decide +kernel
theorem block010_data_flat003_original : block010_data_flat003 = (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) := by
  rw [block010_data_flat003_step]
def block010_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 13712925600))]
theorem block010_data_flat004_step : block010_data_flat004 = (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) := by decide +kernel
theorem block010_data_flat004_original : block010_data_flat004 = (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) := by
  rw [block010_data_flat004_step]
def block010_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 13122490080))]
theorem block010_data_flat005_step : block010_data_flat005 = (CoefficientMerge.scale (13122490080 : Int) atom0739Coded) := by decide +kernel
theorem block010_data_flat005_original : block010_data_flat005 = (CoefficientMerge.scale (13122490080 : Int) atom0739Coded) := by
  rw [block010_data_flat005_step]
def block010_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080))]
theorem block010_data_flat006_step : block010_data_flat006 = (CoefficientMerge.fastMerge block010_data_flat004 block010_data_flat005) := by decide +kernel
theorem block010_data_flat006_original : block010_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)) := by
  rw [block010_data_flat006_step, block010_data_flat004_original, block010_data_flat005_original]
def block010_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080))]
theorem block010_data_flat007_step : block010_data_flat007 = (CoefficientMerge.fastMerge block010_data_flat003 block010_data_flat006) := by decide +kernel
theorem block010_data_flat007_original : block010_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded))) := by
  rw [block010_data_flat007_step, block010_data_flat003_original, block010_data_flat006_original]
def block010_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080))]
theorem block010_data_flat008_step : block010_data_flat008 = (CoefficientMerge.fastMerge block010_data_flat002 block010_data_flat007) := by decide +kernel
theorem block010_data_flat008_original : block010_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) := by
  rw [block010_data_flat008_step, block010_data_flat002_original, block010_data_flat007_original]
def block010_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 9202835040))]
theorem block010_data_flat009_step : block010_data_flat009 = (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) := by decide +kernel
theorem block010_data_flat009_original : block010_data_flat009 = (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) := by
  rw [block010_data_flat009_step]
def block010_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 14166482400))]
theorem block010_data_flat010_step : block010_data_flat010 = (CoefficientMerge.scale (14166482400 : Int) atom0741Coded) := by decide +kernel
theorem block010_data_flat010_original : block010_data_flat010 = (CoefficientMerge.scale (14166482400 : Int) atom0741Coded) := by
  rw [block010_data_flat010_step]
def block010_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400))]
theorem block010_data_flat011_step : block010_data_flat011 = (CoefficientMerge.fastMerge block010_data_flat009 block010_data_flat010) := by decide +kernel
theorem block010_data_flat011_original : block010_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) := by
  rw [block010_data_flat011_step, block010_data_flat009_original, block010_data_flat010_original]
def block010_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 3690344448))]
theorem block010_data_flat012_step : block010_data_flat012 = (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) := by decide +kernel
theorem block010_data_flat012_original : block010_data_flat012 = (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) := by
  rw [block010_data_flat012_step]
def block010_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 11120967960))]
theorem block010_data_flat013_step : block010_data_flat013 = (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) := by decide +kernel
theorem block010_data_flat013_original : block010_data_flat013 = (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) := by
  rw [block010_data_flat013_step]
def block010_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1545, Int.ofNat (nat_lit 11594877840))]
theorem block010_data_flat014_step : block010_data_flat014 = (CoefficientMerge.scale (11594877840 : Int) atom0744Coded) := by decide +kernel
theorem block010_data_flat014_original : block010_data_flat014 = (CoefficientMerge.scale (11594877840 : Int) atom0744Coded) := by
  rw [block010_data_flat014_step]
def block010_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840))]
theorem block010_data_flat015_step : block010_data_flat015 = (CoefficientMerge.fastMerge block010_data_flat013 block010_data_flat014) := by decide +kernel
theorem block010_data_flat015_original : block010_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded)) := by
  rw [block010_data_flat015_step, block010_data_flat013_original, block010_data_flat014_original]
def block010_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840))]
theorem block010_data_flat016_step : block010_data_flat016 = (CoefficientMerge.fastMerge block010_data_flat012 block010_data_flat015) := by decide +kernel
theorem block010_data_flat016_original : block010_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))) := by
  rw [block010_data_flat016_step, block010_data_flat012_original, block010_data_flat015_original]
def block010_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840))]
theorem block010_data_flat017_step : block010_data_flat017 = (CoefficientMerge.fastMerge block010_data_flat011 block010_data_flat016) := by decide +kernel
theorem block010_data_flat017_original : block010_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded)))) := by
  rw [block010_data_flat017_step, block010_data_flat011_original, block010_data_flat016_original]
def block010_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840))]
theorem block010_data_flat018_step : block010_data_flat018 = (CoefficientMerge.fastMerge block010_data_flat008 block010_data_flat017) := by decide +kernel
theorem block010_data_flat018_original : block010_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) := by
  rw [block010_data_flat018_step, block010_data_flat008_original, block010_data_flat017_original]
def block010_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 8682470720))]
theorem block010_data_flat019_step : block010_data_flat019 = (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) := by decide +kernel
theorem block010_data_flat019_original : block010_data_flat019 = (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) := by
  rw [block010_data_flat019_step]
def block010_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1547, Int.ofNat (nat_lit 10514692440))]
theorem block010_data_flat020_step : block010_data_flat020 = (CoefficientMerge.scale (10514692440 : Int) atom0746Coded) := by decide +kernel
theorem block010_data_flat020_original : block010_data_flat020 = (CoefficientMerge.scale (10514692440 : Int) atom0746Coded) := by
  rw [block010_data_flat020_step]
def block010_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440))]
theorem block010_data_flat021_step : block010_data_flat021 = (CoefficientMerge.fastMerge block010_data_flat019 block010_data_flat020) := by decide +kernel
theorem block010_data_flat021_original : block010_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) := by
  rw [block010_data_flat021_step, block010_data_flat019_original, block010_data_flat020_original]
def block010_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1562, Int.ofNat (nat_lit 7996131000))]
theorem block010_data_flat022_step : block010_data_flat022 = (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) := by decide +kernel
theorem block010_data_flat022_original : block010_data_flat022 = (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) := by
  rw [block010_data_flat022_step]
def block010_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1563, Int.ofNat (nat_lit 12540252120))]
theorem block010_data_flat023_step : block010_data_flat023 = (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) := by decide +kernel
theorem block010_data_flat023_original : block010_data_flat023 = (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) := by
  rw [block010_data_flat023_step]
def block010_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1564, Int.ofNat (nat_lit 8869733360))]
theorem block010_data_flat024_step : block010_data_flat024 = (CoefficientMerge.scale (8869733360 : Int) atom0749Coded) := by decide +kernel
theorem block010_data_flat024_original : block010_data_flat024 = (CoefficientMerge.scale (8869733360 : Int) atom0749Coded) := by
  rw [block010_data_flat024_step]
def block010_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360))]
theorem block010_data_flat025_step : block010_data_flat025 = (CoefficientMerge.fastMerge block010_data_flat023 block010_data_flat024) := by decide +kernel
theorem block010_data_flat025_original : block010_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)) := by
  rw [block010_data_flat025_step, block010_data_flat023_original, block010_data_flat024_original]
def block010_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360))]
theorem block010_data_flat026_step : block010_data_flat026 = (CoefficientMerge.fastMerge block010_data_flat022 block010_data_flat025) := by decide +kernel
theorem block010_data_flat026_original : block010_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded))) := by
  rw [block010_data_flat026_step, block010_data_flat022_original, block010_data_flat025_original]
def block010_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360))]
theorem block010_data_flat027_step : block010_data_flat027 = (CoefficientMerge.fastMerge block010_data_flat021 block010_data_flat026) := by decide +kernel
theorem block010_data_flat027_original : block010_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) := by
  rw [block010_data_flat027_step, block010_data_flat021_original, block010_data_flat026_original]
def block010_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 11595222000))]
theorem block010_data_flat028_step : block010_data_flat028 = (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) := by decide +kernel
theorem block010_data_flat028_original : block010_data_flat028 = (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) := by
  rw [block010_data_flat028_step]
def block010_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1581, Int.ofNat (nat_lit 3641223600))]
theorem block010_data_flat029_step : block010_data_flat029 = (CoefficientMerge.scale (3641223600 : Int) atom0751Coded) := by decide +kernel
theorem block010_data_flat029_original : block010_data_flat029 = (CoefficientMerge.scale (3641223600 : Int) atom0751Coded) := by
  rw [block010_data_flat029_step]
def block010_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600))]
theorem block010_data_flat030_step : block010_data_flat030 = (CoefficientMerge.fastMerge block010_data_flat028 block010_data_flat029) := by decide +kernel
theorem block010_data_flat030_original : block010_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) := by
  rw [block010_data_flat030_step, block010_data_flat028_original, block010_data_flat029_original]
def block010_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1582, Int.ofNat (nat_lit 4763779440))]
theorem block010_data_flat031_step : block010_data_flat031 = (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) := by decide +kernel
theorem block010_data_flat031_original : block010_data_flat031 = (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) := by
  rw [block010_data_flat031_step]
def block010_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1583, Int.ofNat (nat_lit 7669965240))]
theorem block010_data_flat032_step : block010_data_flat032 = (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) := by decide +kernel
theorem block010_data_flat032_original : block010_data_flat032 = (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) := by
  rw [block010_data_flat032_step]
def block010_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat033_step : block010_data_flat033 = (CoefficientMerge.scale (2648638440 : Int) atom0754Coded) := by decide +kernel
theorem block010_data_flat033_original : block010_data_flat033 = (CoefficientMerge.scale (2648638440 : Int) atom0754Coded) := by
  rw [block010_data_flat033_step]
def block010_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat034_step : block010_data_flat034 = (CoefficientMerge.fastMerge block010_data_flat032 block010_data_flat033) := by decide +kernel
theorem block010_data_flat034_original : block010_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)) := by
  rw [block010_data_flat034_step, block010_data_flat032_original, block010_data_flat033_original]
def block010_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat035_step : block010_data_flat035 = (CoefficientMerge.fastMerge block010_data_flat031 block010_data_flat034) := by decide +kernel
theorem block010_data_flat035_original : block010_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded))) := by
  rw [block010_data_flat035_step, block010_data_flat031_original, block010_data_flat034_original]
def block010_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat036_step : block010_data_flat036 = (CoefficientMerge.fastMerge block010_data_flat030 block010_data_flat035) := by decide +kernel
theorem block010_data_flat036_original : block010_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))) := by
  rw [block010_data_flat036_step, block010_data_flat030_original, block010_data_flat035_original]
def block010_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat037_step : block010_data_flat037 = (CoefficientMerge.fastMerge block010_data_flat027 block010_data_flat036) := by decide +kernel
theorem block010_data_flat037_original : block010_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded))))) := by
  rw [block010_data_flat037_step, block010_data_flat027_original, block010_data_flat036_original]
def block010_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840)), (nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440))]
theorem block010_data_flat038_step : block010_data_flat038 = (CoefficientMerge.fastMerge block010_data_flat018 block010_data_flat037) := by decide +kernel
theorem block010_data_flat038_original : block010_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) := by
  rw [block010_data_flat038_step, block010_data_flat018_original, block010_data_flat037_original]
def block010_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 2764487880))]
theorem block010_data_flat039_step : block010_data_flat039 = (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) := by decide +kernel
theorem block010_data_flat039_original : block010_data_flat039 = (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) := by
  rw [block010_data_flat039_step]
def block010_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1715, Int.ofNat (nat_lit 580913280))]
theorem block010_data_flat040_step : block010_data_flat040 = (CoefficientMerge.scale (580913280 : Int) atom0756Coded) := by decide +kernel
theorem block010_data_flat040_original : block010_data_flat040 = (CoefficientMerge.scale (580913280 : Int) atom0756Coded) := by
  rw [block010_data_flat040_step]
def block010_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280))]
theorem block010_data_flat041_step : block010_data_flat041 = (CoefficientMerge.fastMerge block010_data_flat039 block010_data_flat040) := by decide +kernel
theorem block010_data_flat041_original : block010_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) := by
  rw [block010_data_flat041_step, block010_data_flat039_original, block010_data_flat040_original]
def block010_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1716, Int.ofNat (nat_lit 807960960))]
theorem block010_data_flat042_step : block010_data_flat042 = (CoefficientMerge.scale (807960960 : Int) atom0757Coded) := by decide +kernel
theorem block010_data_flat042_original : block010_data_flat042 = (CoefficientMerge.scale (807960960 : Int) atom0757Coded) := by
  rw [block010_data_flat042_step]
def block010_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1717, Int.ofNat (nat_lit 103864320))]
theorem block010_data_flat043_step : block010_data_flat043 = (CoefficientMerge.scale (103864320 : Int) atom0758Coded) := by decide +kernel
theorem block010_data_flat043_original : block010_data_flat043 = (CoefficientMerge.scale (103864320 : Int) atom0758Coded) := by
  rw [block010_data_flat043_step]
def block010_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1718, Int.ofNat (nat_lit 78704640))]
theorem block010_data_flat044_step : block010_data_flat044 = (CoefficientMerge.scale (78704640 : Int) atom0759Coded) := by decide +kernel
theorem block010_data_flat044_original : block010_data_flat044 = (CoefficientMerge.scale (78704640 : Int) atom0759Coded) := by
  rw [block010_data_flat044_step]
def block010_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640))]
theorem block010_data_flat045_step : block010_data_flat045 = (CoefficientMerge.fastMerge block010_data_flat043 block010_data_flat044) := by decide +kernel
theorem block010_data_flat045_original : block010_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)) := by
  rw [block010_data_flat045_step, block010_data_flat043_original, block010_data_flat044_original]
def block010_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640))]
theorem block010_data_flat046_step : block010_data_flat046 = (CoefficientMerge.fastMerge block010_data_flat042 block010_data_flat045) := by decide +kernel
theorem block010_data_flat046_original : block010_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded))) := by
  rw [block010_data_flat046_step, block010_data_flat042_original, block010_data_flat045_original]
def block010_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640))]
theorem block010_data_flat047_step : block010_data_flat047 = (CoefficientMerge.fastMerge block010_data_flat041 block010_data_flat046) := by decide +kernel
theorem block010_data_flat047_original : block010_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) := by
  rw [block010_data_flat047_step, block010_data_flat041_original, block010_data_flat046_original]
def block010_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 960689520))]
theorem block010_data_flat048_step : block010_data_flat048 = (CoefficientMerge.scale (960689520 : Int) atom0760Coded) := by decide +kernel
theorem block010_data_flat048_original : block010_data_flat048 = (CoefficientMerge.scale (960689520 : Int) atom0760Coded) := by
  rw [block010_data_flat048_step]
def block010_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1734, Int.ofNat (nat_lit 546687360))]
theorem block010_data_flat049_step : block010_data_flat049 = (CoefficientMerge.scale (546687360 : Int) atom0761Coded) := by decide +kernel
theorem block010_data_flat049_original : block010_data_flat049 = (CoefficientMerge.scale (546687360 : Int) atom0761Coded) := by
  rw [block010_data_flat049_step]
def block010_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360))]
theorem block010_data_flat050_step : block010_data_flat050 = (CoefficientMerge.fastMerge block010_data_flat048 block010_data_flat049) := by decide +kernel
theorem block010_data_flat050_original : block010_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) := by
  rw [block010_data_flat050_step, block010_data_flat048_original, block010_data_flat049_original]
def block010_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1738, Int.ofNat (nat_lit 103864320))]
theorem block010_data_flat051_step : block010_data_flat051 = (CoefficientMerge.scale (103864320 : Int) atom0762Coded) := by decide +kernel
theorem block010_data_flat051_original : block010_data_flat051 = (CoefficientMerge.scale (103864320 : Int) atom0762Coded) := by
  rw [block010_data_flat051_step]
def block010_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 207728640))]
theorem block010_data_flat052_step : block010_data_flat052 = (CoefficientMerge.scale (207728640 : Int) atom0763Coded) := by decide +kernel
theorem block010_data_flat052_original : block010_data_flat052 = (CoefficientMerge.scale (207728640 : Int) atom0763Coded) := by
  rw [block010_data_flat052_step]
def block010_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1740, Int.ofNat (nat_lit 1275597792))]
theorem block010_data_flat053_step : block010_data_flat053 = (CoefficientMerge.scale (1275597792 : Int) atom0764Coded) := by decide +kernel
theorem block010_data_flat053_original : block010_data_flat053 = (CoefficientMerge.scale (1275597792 : Int) atom0764Coded) := by
  rw [block010_data_flat053_step]
def block010_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792))]
theorem block010_data_flat054_step : block010_data_flat054 = (CoefficientMerge.fastMerge block010_data_flat052 block010_data_flat053) := by decide +kernel
theorem block010_data_flat054_original : block010_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded)) := by
  rw [block010_data_flat054_step, block010_data_flat052_original, block010_data_flat053_original]
def block010_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792))]
theorem block010_data_flat055_step : block010_data_flat055 = (CoefficientMerge.fastMerge block010_data_flat051 block010_data_flat054) := by decide +kernel
theorem block010_data_flat055_original : block010_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))) := by
  rw [block010_data_flat055_step, block010_data_flat051_original, block010_data_flat054_original]
def block010_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792))]
theorem block010_data_flat056_step : block010_data_flat056 = (CoefficientMerge.fastMerge block010_data_flat050 block010_data_flat055) := by decide +kernel
theorem block010_data_flat056_original : block010_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded)))) := by
  rw [block010_data_flat056_step, block010_data_flat050_original, block010_data_flat055_original]
def block010_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792))]
theorem block010_data_flat057_step : block010_data_flat057 = (CoefficientMerge.fastMerge block010_data_flat047 block010_data_flat056) := by decide +kernel
theorem block010_data_flat057_original : block010_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) := by
  rw [block010_data_flat057_step, block010_data_flat047_original, block010_data_flat056_original]
def block010_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1742, Int.ofNat (nat_lit 173304000))]
theorem block010_data_flat058_step : block010_data_flat058 = (CoefficientMerge.scale (173304000 : Int) atom0765Coded) := by decide +kernel
theorem block010_data_flat058_original : block010_data_flat058 = (CoefficientMerge.scale (173304000 : Int) atom0765Coded) := by
  rw [block010_data_flat058_step]
def block010_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1743, Int.ofNat (nat_lit 1180247040))]
theorem block010_data_flat059_step : block010_data_flat059 = (CoefficientMerge.scale (1180247040 : Int) atom0766Coded) := by decide +kernel
theorem block010_data_flat059_original : block010_data_flat059 = (CoefficientMerge.scale (1180247040 : Int) atom0766Coded) := by
  rw [block010_data_flat059_step]
def block010_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040))]
theorem block010_data_flat060_step : block010_data_flat060 = (CoefficientMerge.fastMerge block010_data_flat058 block010_data_flat059) := by decide +kernel
theorem block010_data_flat060_original : block010_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) := by
  rw [block010_data_flat060_step, block010_data_flat058_original, block010_data_flat059_original]
def block010_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1744, Int.ofNat (nat_lit 2293143552))]
theorem block010_data_flat061_step : block010_data_flat061 = (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) := by decide +kernel
theorem block010_data_flat061_original : block010_data_flat061 = (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) := by
  rw [block010_data_flat061_step]
def block010_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1745, Int.ofNat (nat_lit 3586383360))]
theorem block010_data_flat062_step : block010_data_flat062 = (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) := by decide +kernel
theorem block010_data_flat062_original : block010_data_flat062 = (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) := by
  rw [block010_data_flat062_step]
def block010_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 126817920))]
theorem block010_data_flat063_step : block010_data_flat063 = (CoefficientMerge.scale (126817920 : Int) atom0769Coded) := by decide +kernel
theorem block010_data_flat063_original : block010_data_flat063 = (CoefficientMerge.scale (126817920 : Int) atom0769Coded) := by
  rw [block010_data_flat063_step]
def block010_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920))]
theorem block010_data_flat064_step : block010_data_flat064 = (CoefficientMerge.fastMerge block010_data_flat062 block010_data_flat063) := by decide +kernel
theorem block010_data_flat064_original : block010_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)) := by
  rw [block010_data_flat064_step, block010_data_flat062_original, block010_data_flat063_original]
def block010_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920))]
theorem block010_data_flat065_step : block010_data_flat065 = (CoefficientMerge.fastMerge block010_data_flat061 block010_data_flat064) := by decide +kernel
theorem block010_data_flat065_original : block010_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded))) := by
  rw [block010_data_flat065_step, block010_data_flat061_original, block010_data_flat064_original]
def block010_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920))]
theorem block010_data_flat066_step : block010_data_flat066 = (CoefficientMerge.fastMerge block010_data_flat060 block010_data_flat065) := by decide +kernel
theorem block010_data_flat066_original : block010_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) := by
  rw [block010_data_flat066_step, block010_data_flat060_original, block010_data_flat065_original]
def block010_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1756, Int.ofNat (nat_lit 157409280))]
theorem block010_data_flat067_step : block010_data_flat067 = (CoefficientMerge.scale (157409280 : Int) atom0770Coded) := by decide +kernel
theorem block010_data_flat067_original : block010_data_flat067 = (CoefficientMerge.scale (157409280 : Int) atom0770Coded) := by
  rw [block010_data_flat067_step]
def block010_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1757, Int.ofNat (nat_lit 314818560))]
theorem block010_data_flat068_step : block010_data_flat068 = (CoefficientMerge.scale (314818560 : Int) atom0771Coded) := by decide +kernel
theorem block010_data_flat068_original : block010_data_flat068 = (CoefficientMerge.scale (314818560 : Int) atom0771Coded) := by
  rw [block010_data_flat068_step]
def block010_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560))]
theorem block010_data_flat069_step : block010_data_flat069 = (CoefficientMerge.fastMerge block010_data_flat067 block010_data_flat068) := by decide +kernel
theorem block010_data_flat069_original : block010_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) := by
  rw [block010_data_flat069_step, block010_data_flat067_original, block010_data_flat068_original]
def block010_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1758, Int.ofNat (nat_lit 1398790080))]
theorem block010_data_flat070_step : block010_data_flat070 = (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) := by decide +kernel
theorem block010_data_flat070_original : block010_data_flat070 = (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) := by
  rw [block010_data_flat070_step]
def block010_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1759, Int.ofNat (nat_lit 748771920))]
theorem block010_data_flat071_step : block010_data_flat071 = (CoefficientMerge.scale (748771920 : Int) atom0773Coded) := by decide +kernel
theorem block010_data_flat071_original : block010_data_flat071 = (CoefficientMerge.scale (748771920 : Int) atom0773Coded) := by
  rw [block010_data_flat071_step]
def block010_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat072_step : block010_data_flat072 = (CoefficientMerge.scale (1544502240 : Int) atom0774Coded) := by decide +kernel
theorem block010_data_flat072_original : block010_data_flat072 = (CoefficientMerge.scale (1544502240 : Int) atom0774Coded) := by
  rw [block010_data_flat072_step]
def block010_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat073_step : block010_data_flat073 = (CoefficientMerge.fastMerge block010_data_flat071 block010_data_flat072) := by decide +kernel
theorem block010_data_flat073_original : block010_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded)) := by
  rw [block010_data_flat073_step, block010_data_flat071_original, block010_data_flat072_original]
def block010_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat074_step : block010_data_flat074 = (CoefficientMerge.fastMerge block010_data_flat070 block010_data_flat073) := by decide +kernel
theorem block010_data_flat074_original : block010_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))) := by
  rw [block010_data_flat074_step, block010_data_flat070_original, block010_data_flat073_original]
def block010_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat075_step : block010_data_flat075 = (CoefficientMerge.fastMerge block010_data_flat069 block010_data_flat074) := by decide +kernel
theorem block010_data_flat075_original : block010_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded)))) := by
  rw [block010_data_flat075_step, block010_data_flat069_original, block010_data_flat074_original]
def block010_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat076_step : block010_data_flat076 = (CoefficientMerge.fastMerge block010_data_flat066 block010_data_flat075) := by decide +kernel
theorem block010_data_flat076_original : block010_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))) := by
  rw [block010_data_flat076_step, block010_data_flat066_original, block010_data_flat075_original]
def block010_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792)), (nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat077_step : block010_data_flat077 = (CoefficientMerge.fastMerge block010_data_flat057 block010_data_flat076) := by decide +kernel
theorem block010_data_flat077_original : block010_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded)))))) := by
  rw [block010_data_flat077_step, block010_data_flat057_original, block010_data_flat076_original]
def block010_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840)), (nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440)), (nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792)), (nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240))]
theorem block010_data_flat078_step : block010_data_flat078 = (CoefficientMerge.fastMerge block010_data_flat038 block010_data_flat077) := by decide +kernel
theorem block010_data_flat078_original : block010_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))))) := by
  rw [block010_data_flat078_step, block010_data_flat038_original, block010_data_flat077_original]
def block010_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080))]
theorem block010_data_flat079_step : block010_data_flat079 = (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) := by decide +kernel
theorem block010_data_flat079_original : block010_data_flat079 = (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) := by
  rw [block010_data_flat079_step]
def block010_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1762, Int.ofNat (nat_lit 4822144560))]
theorem block010_data_flat080_step : block010_data_flat080 = (CoefficientMerge.scale (4822144560 : Int) atom0776Coded) := by decide +kernel
theorem block010_data_flat080_original : block010_data_flat080 = (CoefficientMerge.scale (4822144560 : Int) atom0776Coded) := by
  rw [block010_data_flat080_step]
def block010_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560))]
theorem block010_data_flat081_step : block010_data_flat081 = (CoefficientMerge.fastMerge block010_data_flat079 block010_data_flat080) := by decide +kernel
theorem block010_data_flat081_original : block010_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) := by
  rw [block010_data_flat081_step, block010_data_flat079_original, block010_data_flat080_original]
def block010_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1763, Int.ofNat (nat_lit 6797629440))]
theorem block010_data_flat082_step : block010_data_flat082 = (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) := by decide +kernel
theorem block010_data_flat082_original : block010_data_flat082 = (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) := by
  rw [block010_data_flat082_step]
def block010_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1772, Int.ofNat (nat_lit 546687360))]
theorem block010_data_flat083_step : block010_data_flat083 = (CoefficientMerge.scale (546687360 : Int) atom0778Coded) := by decide +kernel
theorem block010_data_flat083_original : block010_data_flat083 = (CoefficientMerge.scale (546687360 : Int) atom0778Coded) := by
  rw [block010_data_flat083_step]
def block010_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1773, Int.ofNat (nat_lit 832953600))]
theorem block010_data_flat084_step : block010_data_flat084 = (CoefficientMerge.scale (832953600 : Int) atom0779Coded) := by decide +kernel
theorem block010_data_flat084_original : block010_data_flat084 = (CoefficientMerge.scale (832953600 : Int) atom0779Coded) := by
  rw [block010_data_flat084_step]
def block010_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600))]
theorem block010_data_flat085_step : block010_data_flat085 = (CoefficientMerge.fastMerge block010_data_flat083 block010_data_flat084) := by decide +kernel
theorem block010_data_flat085_original : block010_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)) := by
  rw [block010_data_flat085_step, block010_data_flat083_original, block010_data_flat084_original]
def block010_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600))]
theorem block010_data_flat086_step : block010_data_flat086 = (CoefficientMerge.fastMerge block010_data_flat082 block010_data_flat085) := by decide +kernel
theorem block010_data_flat086_original : block010_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded))) := by
  rw [block010_data_flat086_step, block010_data_flat082_original, block010_data_flat085_original]
def block010_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600))]
theorem block010_data_flat087_step : block010_data_flat087 = (CoefficientMerge.fastMerge block010_data_flat081 block010_data_flat086) := by decide +kernel
theorem block010_data_flat087_original : block010_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) := by
  rw [block010_data_flat087_step, block010_data_flat081_original, block010_data_flat086_original]
def block010_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1774, Int.ofNat (nat_lit 993588480))]
theorem block010_data_flat088_step : block010_data_flat088 = (CoefficientMerge.scale (993588480 : Int) atom0780Coded) := by decide +kernel
theorem block010_data_flat088_original : block010_data_flat088 = (CoefficientMerge.scale (993588480 : Int) atom0780Coded) := by
  rw [block010_data_flat088_step]
def block010_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1775, Int.ofNat (nat_lit 1154223360))]
theorem block010_data_flat089_step : block010_data_flat089 = (CoefficientMerge.scale (1154223360 : Int) atom0781Coded) := by decide +kernel
theorem block010_data_flat089_original : block010_data_flat089 = (CoefficientMerge.scale (1154223360 : Int) atom0781Coded) := by
  rw [block010_data_flat089_step]
def block010_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360))]
theorem block010_data_flat090_step : block010_data_flat090 = (CoefficientMerge.fastMerge block010_data_flat088 block010_data_flat089) := by decide +kernel
theorem block010_data_flat090_original : block010_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) := by
  rw [block010_data_flat090_step, block010_data_flat088_original, block010_data_flat089_original]
def block010_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1776, Int.ofNat (nat_lit 2225592000))]
theorem block010_data_flat091_step : block010_data_flat091 = (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) := by decide +kernel
theorem block010_data_flat091_original : block010_data_flat091 = (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) := by
  rw [block010_data_flat091_step]
def block010_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1777, Int.ofNat (nat_lit 1908204720))]
theorem block010_data_flat092_step : block010_data_flat092 = (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) := by decide +kernel
theorem block010_data_flat092_original : block010_data_flat092 = (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) := by
  rw [block010_data_flat092_step]
def block010_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1778, Int.ofNat (nat_lit 3183133920))]
theorem block010_data_flat093_step : block010_data_flat093 = (CoefficientMerge.scale (3183133920 : Int) atom0784Coded) := by decide +kernel
theorem block010_data_flat093_original : block010_data_flat093 = (CoefficientMerge.scale (3183133920 : Int) atom0784Coded) := by
  rw [block010_data_flat093_step]
def block010_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920))]
theorem block010_data_flat094_step : block010_data_flat094 = (CoefficientMerge.fastMerge block010_data_flat092 block010_data_flat093) := by decide +kernel
theorem block010_data_flat094_original : block010_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded)) := by
  rw [block010_data_flat094_step, block010_data_flat092_original, block010_data_flat093_original]
def block010_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920))]
theorem block010_data_flat095_step : block010_data_flat095 = (CoefficientMerge.fastMerge block010_data_flat091 block010_data_flat094) := by decide +kernel
theorem block010_data_flat095_original : block010_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))) := by
  rw [block010_data_flat095_step, block010_data_flat091_original, block010_data_flat094_original]
def block010_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920))]
theorem block010_data_flat096_step : block010_data_flat096 = (CoefficientMerge.fastMerge block010_data_flat090 block010_data_flat095) := by decide +kernel
theorem block010_data_flat096_original : block010_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded)))) := by
  rw [block010_data_flat096_step, block010_data_flat090_original, block010_data_flat095_original]
def block010_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920))]
theorem block010_data_flat097_step : block010_data_flat097 = (CoefficientMerge.fastMerge block010_data_flat087 block010_data_flat096) := by decide +kernel
theorem block010_data_flat097_original : block010_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) := by
  rw [block010_data_flat097_step, block010_data_flat087_original, block010_data_flat096_original]
def block010_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1779, Int.ofNat (nat_lit 4551344880))]
theorem block010_data_flat098_step : block010_data_flat098 = (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) := by decide +kernel
theorem block010_data_flat098_original : block010_data_flat098 = (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) := by
  rw [block010_data_flat098_step]
def block010_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1780, Int.ofNat (nat_lit 6551182800))]
theorem block010_data_flat099_step : block010_data_flat099 = (CoefficientMerge.scale (6551182800 : Int) atom0786Coded) := by decide +kernel
theorem block010_data_flat099_original : block010_data_flat099 = (CoefficientMerge.scale (6551182800 : Int) atom0786Coded) := by
  rw [block010_data_flat099_step]
def block010_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800))]
theorem block010_data_flat100_step : block010_data_flat100 = (CoefficientMerge.fastMerge block010_data_flat098 block010_data_flat099) := by decide +kernel
theorem block010_data_flat100_original : block010_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) := by
  rw [block010_data_flat100_step, block010_data_flat098_original, block010_data_flat099_original]
def block010_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1781, Int.ofNat (nat_lit 8696665440))]
theorem block010_data_flat101_step : block010_data_flat101 = (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) := by decide +kernel
theorem block010_data_flat101_original : block010_data_flat101 = (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) := by
  rw [block010_data_flat101_step]
def block010_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1791, Int.ofNat (nat_lit 1063635840))]
theorem block010_data_flat102_step : block010_data_flat102 = (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) := by decide +kernel
theorem block010_data_flat102_original : block010_data_flat102 = (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) := by
  rw [block010_data_flat102_step]
def block010_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1792, Int.ofNat (nat_lit 1890097920))]
theorem block010_data_flat103_step : block010_data_flat103 = (CoefficientMerge.scale (1890097920 : Int) atom0789Coded) := by decide +kernel
theorem block010_data_flat103_original : block010_data_flat103 = (CoefficientMerge.scale (1890097920 : Int) atom0789Coded) := by
  rw [block010_data_flat103_step]
def block010_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920))]
theorem block010_data_flat104_step : block010_data_flat104 = (CoefficientMerge.fastMerge block010_data_flat102 block010_data_flat103) := by decide +kernel
theorem block010_data_flat104_original : block010_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)) := by
  rw [block010_data_flat104_step, block010_data_flat102_original, block010_data_flat103_original]
def block010_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920))]
theorem block010_data_flat105_step : block010_data_flat105 = (CoefficientMerge.fastMerge block010_data_flat101 block010_data_flat104) := by decide +kernel
theorem block010_data_flat105_original : block010_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded))) := by
  rw [block010_data_flat105_step, block010_data_flat101_original, block010_data_flat104_original]
def block010_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920))]
theorem block010_data_flat106_step : block010_data_flat106 = (CoefficientMerge.fastMerge block010_data_flat100 block010_data_flat105) := by decide +kernel
theorem block010_data_flat106_original : block010_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) := by
  rw [block010_data_flat106_step, block010_data_flat100_original, block010_data_flat105_original]
def block010_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1793, Int.ofNat (nat_lit 2003639040))]
theorem block010_data_flat107_step : block010_data_flat107 = (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) := by decide +kernel
theorem block010_data_flat107_original : block010_data_flat107 = (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) := by
  rw [block010_data_flat107_step]
def block010_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1794, Int.ofNat (nat_lit 3152367360))]
theorem block010_data_flat108_step : block010_data_flat108 = (CoefficientMerge.scale (3152367360 : Int) atom0791Coded) := by decide +kernel
theorem block010_data_flat108_original : block010_data_flat108 = (CoefficientMerge.scale (3152367360 : Int) atom0791Coded) := by
  rw [block010_data_flat108_step]
def block010_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360))]
theorem block010_data_flat109_step : block010_data_flat109 = (CoefficientMerge.fastMerge block010_data_flat107 block010_data_flat108) := by decide +kernel
theorem block010_data_flat109_original : block010_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) := by
  rw [block010_data_flat109_step, block010_data_flat107_original, block010_data_flat108_original]
def block010_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1795, Int.ofNat (nat_lit 2936154480))]
theorem block010_data_flat110_step : block010_data_flat110 = (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) := by decide +kernel
theorem block010_data_flat110_original : block010_data_flat110 = (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) := by
  rw [block010_data_flat110_step]
def block010_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1796, Int.ofNat (nat_lit 4697875680))]
theorem block010_data_flat111_step : block010_data_flat111 = (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) := by decide +kernel
theorem block010_data_flat111_original : block010_data_flat111 = (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) := by
  rw [block010_data_flat111_step]
def block010_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat112_step : block010_data_flat112 = (CoefficientMerge.scale (5778953520 : Int) atom0794Coded) := by decide +kernel
theorem block010_data_flat112_original : block010_data_flat112 = (CoefficientMerge.scale (5778953520 : Int) atom0794Coded) := by
  rw [block010_data_flat112_step]
def block010_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat113_step : block010_data_flat113 = (CoefficientMerge.fastMerge block010_data_flat111 block010_data_flat112) := by decide +kernel
theorem block010_data_flat113_original : block010_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)) := by
  rw [block010_data_flat113_step, block010_data_flat111_original, block010_data_flat112_original]
def block010_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat114_step : block010_data_flat114 = (CoefficientMerge.fastMerge block010_data_flat110 block010_data_flat113) := by decide +kernel
theorem block010_data_flat114_original : block010_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded))) := by
  rw [block010_data_flat114_step, block010_data_flat110_original, block010_data_flat113_original]
def block010_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat115_step : block010_data_flat115 = (CoefficientMerge.fastMerge block010_data_flat109 block010_data_flat114) := by decide +kernel
theorem block010_data_flat115_original : block010_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))) := by
  rw [block010_data_flat115_step, block010_data_flat109_original, block010_data_flat114_original]
def block010_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat116_step : block010_data_flat116 = (CoefficientMerge.fastMerge block010_data_flat106 block010_data_flat115) := by decide +kernel
theorem block010_data_flat116_original : block010_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded))))) := by
  rw [block010_data_flat116_step, block010_data_flat106_original, block010_data_flat115_original]
def block010_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920)), (nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520))]
theorem block010_data_flat117_step : block010_data_flat117 = (CoefficientMerge.fastMerge block010_data_flat097 block010_data_flat116) := by decide +kernel
theorem block010_data_flat117_original : block010_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) := by
  rw [block010_data_flat117_step, block010_data_flat097_original, block010_data_flat116_original]
def block010_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 7877275920))]
theorem block010_data_flat118_step : block010_data_flat118 = (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) := by decide +kernel
theorem block010_data_flat118_original : block010_data_flat118 = (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) := by
  rw [block010_data_flat118_step]
def block010_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1799, Int.ofNat (nat_lit 10096083360))]
theorem block010_data_flat119_step : block010_data_flat119 = (CoefficientMerge.scale (10096083360 : Int) atom0796Coded) := by decide +kernel
theorem block010_data_flat119_original : block010_data_flat119 = (CoefficientMerge.scale (10096083360 : Int) atom0796Coded) := by
  rw [block010_data_flat119_step]
def block010_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360))]
theorem block010_data_flat120_step : block010_data_flat120 = (CoefficientMerge.fastMerge block010_data_flat118 block010_data_flat119) := by decide +kernel
theorem block010_data_flat120_original : block010_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) := by
  rw [block010_data_flat120_step, block010_data_flat118_original, block010_data_flat119_original]
def block010_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1810, Int.ofNat (nat_lit 1707696000))]
theorem block010_data_flat121_step : block010_data_flat121 = (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) := by decide +kernel
theorem block010_data_flat121_original : block010_data_flat121 = (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) := by
  rw [block010_data_flat121_step]
def block010_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1811, Int.ofNat (nat_lit 3097532160))]
theorem block010_data_flat122_step : block010_data_flat122 = (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) := by decide +kernel
theorem block010_data_flat122_original : block010_data_flat122 = (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) := by
  rw [block010_data_flat122_step]
def block010_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1812, Int.ofNat (nat_lit 4211694720))]
theorem block010_data_flat123_step : block010_data_flat123 = (CoefficientMerge.scale (4211694720 : Int) atom0799Coded) := by decide +kernel
theorem block010_data_flat123_original : block010_data_flat123 = (CoefficientMerge.scale (4211694720 : Int) atom0799Coded) := by
  rw [block010_data_flat123_step]
def block010_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720))]
theorem block010_data_flat124_step : block010_data_flat124 = (CoefficientMerge.fastMerge block010_data_flat122 block010_data_flat123) := by decide +kernel
theorem block010_data_flat124_original : block010_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)) := by
  rw [block010_data_flat124_step, block010_data_flat122_original, block010_data_flat123_original]
def block010_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720))]
theorem block010_data_flat125_step : block010_data_flat125 = (CoefficientMerge.fastMerge block010_data_flat121 block010_data_flat124) := by decide +kernel
theorem block010_data_flat125_original : block010_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded))) := by
  rw [block010_data_flat125_step, block010_data_flat121_original, block010_data_flat124_original]
def block010_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720))]
theorem block010_data_flat126_step : block010_data_flat126 = (CoefficientMerge.fastMerge block010_data_flat120 block010_data_flat125) := by decide +kernel
theorem block010_data_flat126_original : block010_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) := by
  rw [block010_data_flat126_step, block010_data_flat120_original, block010_data_flat125_original]
def block010_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1813, Int.ofNat (nat_lit 3949897200))]
theorem block010_data_flat127_step : block010_data_flat127 = (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) := by decide +kernel
theorem block010_data_flat127_original : block010_data_flat127 = (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) := by
  rw [block010_data_flat127_step]
def block010_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1814, Int.ofNat (nat_lit 6236164320))]
theorem block010_data_flat128_step : block010_data_flat128 = (CoefficientMerge.scale (6236164320 : Int) atom0801Coded) := by decide +kernel
theorem block010_data_flat128_original : block010_data_flat128 = (CoefficientMerge.scale (6236164320 : Int) atom0801Coded) := by
  rw [block010_data_flat128_step]
def block010_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320))]
theorem block010_data_flat129_step : block010_data_flat129 = (CoefficientMerge.fastMerge block010_data_flat127 block010_data_flat128) := by decide +kernel
theorem block010_data_flat129_original : block010_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) := by
  rw [block010_data_flat129_step, block010_data_flat127_original, block010_data_flat128_original]
def block010_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1815, Int.ofNat (nat_lit 6642556080))]
theorem block010_data_flat130_step : block010_data_flat130 = (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) := by decide +kernel
theorem block010_data_flat130_original : block010_data_flat130 = (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) := by
  rw [block010_data_flat130_step]
def block010_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1816, Int.ofNat (nat_lit 8636322960))]
theorem block010_data_flat131_step : block010_data_flat131 = (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) := by decide +kernel
theorem block010_data_flat131_original : block010_data_flat131 = (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) := by
  rw [block010_data_flat131_step]
def block010_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1817, Int.ofNat (nat_lit 11022864480))]
theorem block010_data_flat132_step : block010_data_flat132 = (CoefficientMerge.scale (11022864480 : Int) atom0804Coded) := by decide +kernel
theorem block010_data_flat132_original : block010_data_flat132 = (CoefficientMerge.scale (11022864480 : Int) atom0804Coded) := by
  rw [block010_data_flat132_step]
def block010_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480))]
theorem block010_data_flat133_step : block010_data_flat133 = (CoefficientMerge.fastMerge block010_data_flat131 block010_data_flat132) := by decide +kernel
theorem block010_data_flat133_original : block010_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded)) := by
  rw [block010_data_flat133_step, block010_data_flat131_original, block010_data_flat132_original]
def block010_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480))]
theorem block010_data_flat134_step : block010_data_flat134 = (CoefficientMerge.fastMerge block010_data_flat130 block010_data_flat133) := by decide +kernel
theorem block010_data_flat134_original : block010_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))) := by
  rw [block010_data_flat134_step, block010_data_flat130_original, block010_data_flat133_original]
def block010_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480))]
theorem block010_data_flat135_step : block010_data_flat135 = (CoefficientMerge.fastMerge block010_data_flat129 block010_data_flat134) := by decide +kernel
theorem block010_data_flat135_original : block010_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded)))) := by
  rw [block010_data_flat135_step, block010_data_flat129_original, block010_data_flat134_original]
def block010_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480))]
theorem block010_data_flat136_step : block010_data_flat136 = (CoefficientMerge.fastMerge block010_data_flat126 block010_data_flat135) := by decide +kernel
theorem block010_data_flat136_original : block010_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) := by
  rw [block010_data_flat136_step, block010_data_flat126_original, block010_data_flat135_original]
def block010_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1829, Int.ofNat (nat_lit 2604689280))]
theorem block010_data_flat137_step : block010_data_flat137 = (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) := by decide +kernel
theorem block010_data_flat137_original : block010_data_flat137 = (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) := by
  rw [block010_data_flat137_step]
def block010_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1830, Int.ofNat (nat_lit 5147904960))]
theorem block010_data_flat138_step : block010_data_flat138 = (CoefficientMerge.scale (5147904960 : Int) atom0806Coded) := by decide +kernel
theorem block010_data_flat138_original : block010_data_flat138 = (CoefficientMerge.scale (5147904960 : Int) atom0806Coded) := by
  rw [block010_data_flat138_step]
def block010_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960))]
theorem block010_data_flat139_step : block010_data_flat139 = (CoefficientMerge.fastMerge block010_data_flat137 block010_data_flat138) := by decide +kernel
theorem block010_data_flat139_original : block010_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) := by
  rw [block010_data_flat139_step, block010_data_flat137_original, block010_data_flat138_original]
def block010_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1831, Int.ofNat (nat_lit 4759343280))]
theorem block010_data_flat140_step : block010_data_flat140 = (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) := by decide +kernel
theorem block010_data_flat140_original : block010_data_flat140 = (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) := by
  rw [block010_data_flat140_step]
def block010_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1832, Int.ofNat (nat_lit 7588308960))]
theorem block010_data_flat141_step : block010_data_flat141 = (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) := by decide +kernel
theorem block010_data_flat141_original : block010_data_flat141 = (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) := by
  rw [block010_data_flat141_step]
def block010_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1833, Int.ofNat (nat_lit 8197968240))]
theorem block010_data_flat142_step : block010_data_flat142 = (CoefficientMerge.scale (8197968240 : Int) atom0809Coded) := by decide +kernel
theorem block010_data_flat142_original : block010_data_flat142 = (CoefficientMerge.scale (8197968240 : Int) atom0809Coded) := by
  rw [block010_data_flat142_step]
def block010_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240))]
theorem block010_data_flat143_step : block010_data_flat143 = (CoefficientMerge.fastMerge block010_data_flat141 block010_data_flat142) := by decide +kernel
theorem block010_data_flat143_original : block010_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)) := by
  rw [block010_data_flat143_step, block010_data_flat141_original, block010_data_flat142_original]
def block010_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240))]
theorem block010_data_flat144_step : block010_data_flat144 = (CoefficientMerge.fastMerge block010_data_flat140 block010_data_flat143) := by decide +kernel
theorem block010_data_flat144_original : block010_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded))) := by
  rw [block010_data_flat144_step, block010_data_flat140_original, block010_data_flat143_original]
def block010_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240))]
theorem block010_data_flat145_step : block010_data_flat145 = (CoefficientMerge.fastMerge block010_data_flat139 block010_data_flat144) := by decide +kernel
theorem block010_data_flat145_original : block010_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) := by
  rw [block010_data_flat145_step, block010_data_flat139_original, block010_data_flat144_original]
def block010_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1834, Int.ofNat (nat_lit 8997500880))]
theorem block010_data_flat146_step : block010_data_flat146 = (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) := by decide +kernel
theorem block010_data_flat146_original : block010_data_flat146 = (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) := by
  rw [block010_data_flat146_step]
def block010_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1835, Int.ofNat (nat_lit 13443213600))]
theorem block010_data_flat147_step : block010_data_flat147 = (CoefficientMerge.scale (13443213600 : Int) atom0811Coded) := by decide +kernel
theorem block010_data_flat147_original : block010_data_flat147 = (CoefficientMerge.scale (13443213600 : Int) atom0811Coded) := by
  rw [block010_data_flat147_step]
def block010_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600))]
theorem block010_data_flat148_step : block010_data_flat148 = (CoefficientMerge.fastMerge block010_data_flat146 block010_data_flat147) := by decide +kernel
theorem block010_data_flat148_original : block010_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) := by
  rw [block010_data_flat148_step, block010_data_flat146_original, block010_data_flat147_original]
def block010_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1848, Int.ofNat (nat_lit 4203601920))]
theorem block010_data_flat149_step : block010_data_flat149 = (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) := by decide +kernel
theorem block010_data_flat149_original : block010_data_flat149 = (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) := by
  rw [block010_data_flat149_step]
def block010_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1849, Int.ofNat (nat_lit 7777390680))]
theorem block010_data_flat150_step : block010_data_flat150 = (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) := by decide +kernel
theorem block010_data_flat150_original : block010_data_flat150 = (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) := by
  rw [block010_data_flat150_step]
def block010_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat151_step : block010_data_flat151 = (CoefficientMerge.scale (12945232800 : Int) atom0814Coded) := by decide +kernel
theorem block010_data_flat151_original : block010_data_flat151 = (CoefficientMerge.scale (12945232800 : Int) atom0814Coded) := by
  rw [block010_data_flat151_step]
def block010_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat152_step : block010_data_flat152 = (CoefficientMerge.fastMerge block010_data_flat150 block010_data_flat151) := by decide +kernel
theorem block010_data_flat152_original : block010_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)) := by
  rw [block010_data_flat152_step, block010_data_flat150_original, block010_data_flat151_original]
def block010_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat153_step : block010_data_flat153 = (CoefficientMerge.fastMerge block010_data_flat149 block010_data_flat152) := by decide +kernel
theorem block010_data_flat153_original : block010_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded))) := by
  rw [block010_data_flat153_step, block010_data_flat149_original, block010_data_flat152_original]
def block010_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat154_step : block010_data_flat154 = (CoefficientMerge.fastMerge block010_data_flat148 block010_data_flat153) := by decide +kernel
theorem block010_data_flat154_original : block010_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)))) := by
  rw [block010_data_flat154_step, block010_data_flat148_original, block010_data_flat153_original]
def block010_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat155_step : block010_data_flat155 = (CoefficientMerge.fastMerge block010_data_flat145 block010_data_flat154) := by decide +kernel
theorem block010_data_flat155_original : block010_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded))))) := by
  rw [block010_data_flat155_step, block010_data_flat145_original, block010_data_flat154_original]
def block010_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480)), (nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat156_step : block010_data_flat156 = (CoefficientMerge.fastMerge block010_data_flat136 block010_data_flat155) := by decide +kernel
theorem block010_data_flat156_original : block010_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)))))) := by
  rw [block010_data_flat156_step, block010_data_flat136_original, block010_data_flat155_original]
def block010_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920)), (nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520)), (nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480)), (nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat157_step : block010_data_flat157 = (CoefficientMerge.fastMerge block010_data_flat117 block010_data_flat156) := by decide +kernel
theorem block010_data_flat157_original : block010_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded))))))) := by
  rw [block010_data_flat157_step, block010_data_flat117_original, block010_data_flat156_original]
def block010_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840)), (nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440)), (nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792)), (nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240)), (nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920)), (nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520)), (nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480)), (nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat158_step : block010_data_flat158 = (CoefficientMerge.fastMerge block010_data_flat078 block010_data_flat157) := by decide +kernel
theorem block010_data_flat158_original : block010_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)))))))) := by
  rw [block010_data_flat158_step, block010_data_flat078_original, block010_data_flat157_original]
def block010_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 13537883520)), (nat_lit 1524, Int.ofNat (nat_lit 4983552000)), (nat_lit 1525, Int.ofNat (nat_lit 8680213920)), (nat_lit 1526, Int.ofNat (nat_lit 13712925600)), (nat_lit 1527, Int.ofNat (nat_lit 13122490080)), (nat_lit 1528, Int.ofNat (nat_lit 9202835040)), (nat_lit 1529, Int.ofNat (nat_lit 14166482400)), (nat_lit 1543, Int.ofNat (nat_lit 3690344448)), (nat_lit 1544, Int.ofNat (nat_lit 11120967960)), (nat_lit 1545, Int.ofNat (nat_lit 11594877840)), (nat_lit 1546, Int.ofNat (nat_lit 8682470720)), (nat_lit 1547, Int.ofNat (nat_lit 10514692440)), (nat_lit 1562, Int.ofNat (nat_lit 7996131000)), (nat_lit 1563, Int.ofNat (nat_lit 12540252120)), (nat_lit 1564, Int.ofNat (nat_lit 8869733360)), (nat_lit 1565, Int.ofNat (nat_lit 11595222000)), (nat_lit 1581, Int.ofNat (nat_lit 3641223600)), (nat_lit 1582, Int.ofNat (nat_lit 4763779440)), (nat_lit 1583, Int.ofNat (nat_lit 7669965240)), (nat_lit 1601, Int.ofNat (nat_lit 2648638440)), (nat_lit 1619, Int.ofNat (nat_lit 2764487880)), (nat_lit 1715, Int.ofNat (nat_lit 580913280)), (nat_lit 1716, Int.ofNat (nat_lit 807960960)), (nat_lit 1717, Int.ofNat (nat_lit 103864320)), (nat_lit 1718, Int.ofNat (nat_lit 78704640)), (nat_lit 1722, Int.ofNat (nat_lit 960689520)), (nat_lit 1734, Int.ofNat (nat_lit 546687360)), (nat_lit 1738, Int.ofNat (nat_lit 103864320)), (nat_lit 1739, Int.ofNat (nat_lit 207728640)), (nat_lit 1740, Int.ofNat (nat_lit 1275597792)), (nat_lit 1742, Int.ofNat (nat_lit 173304000)), (nat_lit 1743, Int.ofNat (nat_lit 1180247040)), (nat_lit 1744, Int.ofNat (nat_lit 2293143552)), (nat_lit 1745, Int.ofNat (nat_lit 3586383360)), (nat_lit 1753, Int.ofNat (nat_lit 126817920)), (nat_lit 1756, Int.ofNat (nat_lit 157409280)), (nat_lit 1757, Int.ofNat (nat_lit 314818560)), (nat_lit 1758, Int.ofNat (nat_lit 1398790080)), (nat_lit 1759, Int.ofNat (nat_lit 748771920)), (nat_lit 1760, Int.ofNat (nat_lit 1544502240)), (nat_lit 1761, Int.ofNat (nat_lit 3018304080)), (nat_lit 1762, Int.ofNat (nat_lit 4822144560)), (nat_lit 1763, Int.ofNat (nat_lit 6797629440)), (nat_lit 1772, Int.ofNat (nat_lit 546687360)), (nat_lit 1773, Int.ofNat (nat_lit 832953600)), (nat_lit 1774, Int.ofNat (nat_lit 993588480)), (nat_lit 1775, Int.ofNat (nat_lit 1154223360)), (nat_lit 1776, Int.ofNat (nat_lit 2225592000)), (nat_lit 1777, Int.ofNat (nat_lit 1908204720)), (nat_lit 1778, Int.ofNat (nat_lit 3183133920)), (nat_lit 1779, Int.ofNat (nat_lit 4551344880)), (nat_lit 1780, Int.ofNat (nat_lit 6551182800)), (nat_lit 1781, Int.ofNat (nat_lit 8696665440)), (nat_lit 1791, Int.ofNat (nat_lit 1063635840)), (nat_lit 1792, Int.ofNat (nat_lit 1890097920)), (nat_lit 1793, Int.ofNat (nat_lit 2003639040)), (nat_lit 1794, Int.ofNat (nat_lit 3152367360)), (nat_lit 1795, Int.ofNat (nat_lit 2936154480)), (nat_lit 1796, Int.ofNat (nat_lit 4697875680)), (nat_lit 1797, Int.ofNat (nat_lit 5778953520)), (nat_lit 1798, Int.ofNat (nat_lit 7877275920)), (nat_lit 1799, Int.ofNat (nat_lit 10096083360)), (nat_lit 1810, Int.ofNat (nat_lit 1707696000)), (nat_lit 1811, Int.ofNat (nat_lit 3097532160)), (nat_lit 1812, Int.ofNat (nat_lit 4211694720)), (nat_lit 1813, Int.ofNat (nat_lit 3949897200)), (nat_lit 1814, Int.ofNat (nat_lit 6236164320)), (nat_lit 1815, Int.ofNat (nat_lit 6642556080)), (nat_lit 1816, Int.ofNat (nat_lit 8636322960)), (nat_lit 1817, Int.ofNat (nat_lit 11022864480)), (nat_lit 1829, Int.ofNat (nat_lit 2604689280)), (nat_lit 1830, Int.ofNat (nat_lit 5147904960)), (nat_lit 1831, Int.ofNat (nat_lit 4759343280)), (nat_lit 1832, Int.ofNat (nat_lit 7588308960)), (nat_lit 1833, Int.ofNat (nat_lit 8197968240)), (nat_lit 1834, Int.ofNat (nat_lit 8997500880)), (nat_lit 1835, Int.ofNat (nat_lit 13443213600)), (nat_lit 1848, Int.ofNat (nat_lit 4203601920)), (nat_lit 1849, Int.ofNat (nat_lit 7777390680)), (nat_lit 1850, Int.ofNat (nat_lit 12945232800))]
theorem block010_data_flat159_step : block010_data_flat159 = (CoefficientMerge.trim block010_data_flat158) := by decide +kernel
theorem block010_data_flat159_original : block010_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded))))))))) := by
  rw [block010_data_flat159_step, block010_data_flat158_original]
theorem block010_data : block010 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13537883520 : Int) atom0735Coded) (CoefficientMerge.scale (4983552000 : Int) atom0736Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8680213920 : Int) atom0737Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13712925600 : Int) atom0738Coded) (CoefficientMerge.scale (13122490080 : Int) atom0739Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9202835040 : Int) atom0740Coded) (CoefficientMerge.scale (14166482400 : Int) atom0741Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3690344448 : Int) atom0742Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11120967960 : Int) atom0743Coded) (CoefficientMerge.scale (11594877840 : Int) atom0744Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8682470720 : Int) atom0745Coded) (CoefficientMerge.scale (10514692440 : Int) atom0746Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7996131000 : Int) atom0747Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12540252120 : Int) atom0748Coded) (CoefficientMerge.scale (8869733360 : Int) atom0749Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11595222000 : Int) atom0750Coded) (CoefficientMerge.scale (3641223600 : Int) atom0751Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4763779440 : Int) atom0752Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7669965240 : Int) atom0753Coded) (CoefficientMerge.scale (2648638440 : Int) atom0754Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2764487880 : Int) atom0755Coded) (CoefficientMerge.scale (580913280 : Int) atom0756Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (807960960 : Int) atom0757Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0758Coded) (CoefficientMerge.scale (78704640 : Int) atom0759Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (960689520 : Int) atom0760Coded) (CoefficientMerge.scale (546687360 : Int) atom0761Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0762Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0763Coded) (CoefficientMerge.scale (1275597792 : Int) atom0764Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173304000 : Int) atom0765Coded) (CoefficientMerge.scale (1180247040 : Int) atom0766Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2293143552 : Int) atom0767Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0768Coded) (CoefficientMerge.scale (126817920 : Int) atom0769Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (157409280 : Int) atom0770Coded) (CoefficientMerge.scale (314818560 : Int) atom0771Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1398790080 : Int) atom0772Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (748771920 : Int) atom0773Coded) (CoefficientMerge.scale (1544502240 : Int) atom0774Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3018304080 : Int) atom0775Coded) (CoefficientMerge.scale (4822144560 : Int) atom0776Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6797629440 : Int) atom0777Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (546687360 : Int) atom0778Coded) (CoefficientMerge.scale (832953600 : Int) atom0779Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (993588480 : Int) atom0780Coded) (CoefficientMerge.scale (1154223360 : Int) atom0781Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2225592000 : Int) atom0782Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1908204720 : Int) atom0783Coded) (CoefficientMerge.scale (3183133920 : Int) atom0784Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4551344880 : Int) atom0785Coded) (CoefficientMerge.scale (6551182800 : Int) atom0786Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8696665440 : Int) atom0787Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1063635840 : Int) atom0788Coded) (CoefficientMerge.scale (1890097920 : Int) atom0789Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2003639040 : Int) atom0790Coded) (CoefficientMerge.scale (3152367360 : Int) atom0791Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2936154480 : Int) atom0792Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4697875680 : Int) atom0793Coded) (CoefficientMerge.scale (5778953520 : Int) atom0794Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7877275920 : Int) atom0795Coded) (CoefficientMerge.scale (10096083360 : Int) atom0796Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1707696000 : Int) atom0797Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097532160 : Int) atom0798Coded) (CoefficientMerge.scale (4211694720 : Int) atom0799Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3949897200 : Int) atom0800Coded) (CoefficientMerge.scale (6236164320 : Int) atom0801Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6642556080 : Int) atom0802Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8636322960 : Int) atom0803Coded) (CoefficientMerge.scale (11022864480 : Int) atom0804Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2604689280 : Int) atom0805Coded) (CoefficientMerge.scale (5147904960 : Int) atom0806Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4759343280 : Int) atom0807Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7588308960 : Int) atom0808Coded) (CoefficientMerge.scale (8197968240 : Int) atom0809Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8997500880 : Int) atom0810Coded) (CoefficientMerge.scale (13443213600 : Int) atom0811Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4203601920 : Int) atom0812Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777390680 : Int) atom0813Coded) (CoefficientMerge.scale (12945232800 : Int) atom0814Coded)))))))) := by
  have h : block010 = block010_data_flat159 := by decide +kernel
  exact h.trans block010_data_flat159_original
theorem block010_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block010 := by
  rw [block010_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0735Coded_nonneg g hg hA hB) (atom0736Coded_nonneg g hg hA hB)) (add_nonneg (atom0737Coded_nonneg g hg hA hB) (add_nonneg (atom0738Coded_nonneg g hg hA hB) (atom0739Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0740Coded_nonneg g hg hA hB) (atom0741Coded_nonneg g hg hA hB)) (add_nonneg (atom0742Coded_nonneg g hg hA hB) (add_nonneg (atom0743Coded_nonneg g hg hA hB) (atom0744Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0745Coded_nonneg g hg hA hB) (atom0746Coded_nonneg g hg hA hB)) (add_nonneg (atom0747Coded_nonneg g hg hA hB) (add_nonneg (atom0748Coded_nonneg g hg hA hB) (atom0749Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0750Coded_nonneg g hg hA hB) (atom0751Coded_nonneg g hg hA hB)) (add_nonneg (atom0752Coded_nonneg g hg hA hB) (add_nonneg (atom0753Coded_nonneg g hg hA hB) (atom0754Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0755Coded_nonneg g hg hA hB) (atom0756Coded_nonneg g hg hA hB)) (add_nonneg (atom0757Coded_nonneg g hg hA hB) (add_nonneg (atom0758Coded_nonneg g hg hA hB) (atom0759Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0760Coded_nonneg g hg hA hB) (atom0761Coded_nonneg g hg hA hB)) (add_nonneg (atom0762Coded_nonneg g hg hA hB) (add_nonneg (atom0763Coded_nonneg g hg hA hB) (atom0764Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0765Coded_nonneg g hg hA hB) (atom0766Coded_nonneg g hg hA hB)) (add_nonneg (atom0767Coded_nonneg g hg hA hB) (add_nonneg (atom0768Coded_nonneg g hg hA hB) (atom0769Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0770Coded_nonneg g hg hA hB) (atom0771Coded_nonneg g hg hA hB)) (add_nonneg (atom0772Coded_nonneg g hg hA hB) (add_nonneg (atom0773Coded_nonneg g hg hA hB) (atom0774Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0775Coded_nonneg g hg hA hB) (atom0776Coded_nonneg g hg hA hB)) (add_nonneg (atom0777Coded_nonneg g hg hA hB) (add_nonneg (atom0778Coded_nonneg g hg hA hB) (atom0779Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0780Coded_nonneg g hg hA hB) (atom0781Coded_nonneg g hg hA hB)) (add_nonneg (atom0782Coded_nonneg g hg hA hB) (add_nonneg (atom0783Coded_nonneg g hg hA hB) (atom0784Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0785Coded_nonneg g hg hA hB) (atom0786Coded_nonneg g hg hA hB)) (add_nonneg (atom0787Coded_nonneg g hg hA hB) (add_nonneg (atom0788Coded_nonneg g hg hA hB) (atom0789Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0790Coded_nonneg g hg hA hB) (atom0791Coded_nonneg g hg hA hB)) (add_nonneg (atom0792Coded_nonneg g hg hA hB) (add_nonneg (atom0793Coded_nonneg g hg hA hB) (atom0794Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0795Coded_nonneg g hg hA hB) (atom0796Coded_nonneg g hg hA hB)) (add_nonneg (atom0797Coded_nonneg g hg hA hB) (add_nonneg (atom0798Coded_nonneg g hg hA hB) (atom0799Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0800Coded_nonneg g hg hA hB) (atom0801Coded_nonneg g hg hA hB)) (add_nonneg (atom0802Coded_nonneg g hg hA hB) (add_nonneg (atom0803Coded_nonneg g hg hA hB) (atom0804Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0805Coded_nonneg g hg hA hB) (atom0806Coded_nonneg g hg hA hB)) (add_nonneg (atom0807Coded_nonneg g hg hA hB) (add_nonneg (atom0808Coded_nonneg g hg hA hB) (atom0809Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0810Coded_nonneg g hg hA hB) (atom0811Coded_nonneg g hg hA hB)) (add_nonneg (atom0812Coded_nonneg g hg hA hB) (add_nonneg (atom0813Coded_nonneg g hg hA hB) (atom0814Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
