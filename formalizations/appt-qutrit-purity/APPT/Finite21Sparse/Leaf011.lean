-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0736 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0736 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0736 = ((g 2) * (g 14) * (g 18)) := by
  norm_num [atom0736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0736_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51478079385600 : Int) atom0736) := by
  rw [SparsePolynomial.eval_scale, eval_atom0736]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0736Coded : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 1))]
theorem atom0736Coded_decode : atom0736 = SparsePolynomial.decodeCubic 21 atom0736Coded := by decide +kernel
theorem atom0736Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) := by
  have h := atom0736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0737 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0737 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0737 = ((g 2) * (g 14) * (g 19)) := by
  norm_num [atom0737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0737_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39762525196800 : Int) atom0737) := by
  rw [SparsePolynomial.eval_scale, eval_atom0737]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0737Coded : CoefficientMerge.Poly := [(nat_lit 1195, Int.ofNat (nat_lit 1))]
theorem atom0737Coded_decode : atom0737 = SparsePolynomial.decodeCubic 21 atom0737Coded := by decide +kernel
theorem atom0737Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded) := by
  have h := atom0737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0738 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0738 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0738 = ((g 2) * (g 14) * (g 20)) := by
  norm_num [atom0738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0738_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56627433676800 : Int) atom0738) := by
  rw [SparsePolynomial.eval_scale, eval_atom0738]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0738Coded : CoefficientMerge.Poly := [(nat_lit 1196, Int.ofNat (nat_lit 1))]
theorem atom0738Coded_decode : atom0738 = SparsePolynomial.decodeCubic 21 atom0738Coded := by decide +kernel
theorem atom0738Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) := by
  have h := atom0738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0739 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0739 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0739 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0739_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33575181696000 : Int) atom0739) := by
  rw [SparsePolynomial.eval_scale, eval_atom0739]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0739Coded : CoefficientMerge.Poly := [(nat_lit 1212, Int.ofNat (nat_lit 1))]
theorem atom0739Coded_decode : atom0739 = SparsePolynomial.decodeCubic 21 atom0739Coded := by decide +kernel
theorem atom0739Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) := by
  have h := atom0739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0740 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0740 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0740 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0740_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55106209267200 : Int) atom0740) := by
  rw [SparsePolynomial.eval_scale, eval_atom0740]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0740Coded : CoefficientMerge.Poly := [(nat_lit 1213, Int.ofNat (nat_lit 1))]
theorem atom0740Coded_decode : atom0740 = SparsePolynomial.decodeCubic 21 atom0740Coded := by decide +kernel
theorem atom0740Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded) := by
  have h := atom0740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0741 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0741 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0741 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0741_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75090472934400 : Int) atom0741) := by
  rw [SparsePolynomial.eval_scale, eval_atom0741]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0741Coded : CoefficientMerge.Poly := [(nat_lit 1214, Int.ofNat (nat_lit 1))]
theorem atom0741Coded_decode : atom0741 = SparsePolynomial.decodeCubic 21 atom0741Coded := by decide +kernel
theorem atom0741Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) := by
  have h := atom0741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0742 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0742 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0742 = ((g 2) * (g 15) * (g 18)) := by
  norm_num [atom0742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0742_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65114976729600 : Int) atom0742) := by
  rw [SparsePolynomial.eval_scale, eval_atom0742]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0742Coded : CoefficientMerge.Poly := [(nat_lit 1215, Int.ofNat (nat_lit 1))]
theorem atom0742Coded_decode : atom0742 = SparsePolynomial.decodeCubic 21 atom0742Coded := by decide +kernel
theorem atom0742Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded) := by
  have h := atom0742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0743 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0743 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0743 = ((g 2) * (g 15) * (g 19)) := by
  norm_num [atom0743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0743_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39869803411200 : Int) atom0743) := by
  rw [SparsePolynomial.eval_scale, eval_atom0743]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0743Coded : CoefficientMerge.Poly := [(nat_lit 1216, Int.ofNat (nat_lit 1))]
theorem atom0743Coded_decode : atom0743 = SparsePolynomial.decodeCubic 21 atom0743Coded := by decide +kernel
theorem atom0743Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) := by
  have h := atom0743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0744 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0744 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0744 = ((g 2) * (g 15) * (g 20)) := by
  norm_num [atom0744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0744_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60710287881600 : Int) atom0744) := by
  rw [SparsePolynomial.eval_scale, eval_atom0744]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0744Coded : CoefficientMerge.Poly := [(nat_lit 1217, Int.ofNat (nat_lit 1))]
theorem atom0744Coded_decode : atom0744 = SparsePolynomial.decodeCubic 21 atom0744Coded := by decide +kernel
theorem atom0744Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) := by
  have h := atom0744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0745 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0745 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0745 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0745_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22698910402560 : Int) atom0745) := by
  rw [SparsePolynomial.eval_scale, eval_atom0745]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0745Coded : CoefficientMerge.Poly := [(nat_lit 1234, Int.ofNat (nat_lit 1))]
theorem atom0745Coded_decode : atom0745 = SparsePolynomial.decodeCubic 21 atom0745Coded := by decide +kernel
theorem atom0745Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded) := by
  have h := atom0745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0746 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0746 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0746 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0746_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61504901337600 : Int) atom0746) := by
  rw [SparsePolynomial.eval_scale, eval_atom0746]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0746Coded : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 1))]
theorem atom0746Coded_decode : atom0746 = SparsePolynomial.decodeCubic 21 atom0746Coded := by decide +kernel
theorem atom0746Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) := by
  have h := atom0746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0747 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0747 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0747 = ((g 2) * (g 16) * (g 18)) := by
  norm_num [atom0747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0747_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60041007129600 : Int) atom0747) := by
  rw [SparsePolynomial.eval_scale, eval_atom0747]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0747Coded : CoefficientMerge.Poly := [(nat_lit 1236, Int.ofNat (nat_lit 1))]
theorem atom0747Coded_decode : atom0747 = SparsePolynomial.decodeCubic 21 atom0747Coded := by decide +kernel
theorem atom0747Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded) := by
  have h := atom0747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0748 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0748 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0748 = ((g 2) * (g 16) * (g 19)) := by
  norm_num [atom0748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0748_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39977081625600 : Int) atom0748) := by
  rw [SparsePolynomial.eval_scale, eval_atom0748]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0748Coded : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 1))]
theorem atom0748Coded_decode : atom0748 = SparsePolynomial.decodeCubic 21 atom0748Coded := by decide +kernel
theorem atom0748Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) := by
  have h := atom0748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0749 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0749 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0749 = ((g 2) * (g 16) * (g 20)) := by
  norm_num [atom0749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0749_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47368164009600 : Int) atom0749) := by
  rw [SparsePolynomial.eval_scale, eval_atom0749]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0749Coded : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 1))]
theorem atom0749Coded_decode : atom0749 = SparsePolynomial.decodeCubic 21 atom0749Coded := by decide +kernel
theorem atom0749Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) := by
  have h := atom0749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0750 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0750 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0750 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom0750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0750_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39973873766400 : Int) atom0750) := by
  rw [SparsePolynomial.eval_scale, eval_atom0750]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0750Coded : CoefficientMerge.Poly := [(nat_lit 1256, Int.ofNat (nat_lit 1))]
theorem atom0750Coded_decode : atom0750 = SparsePolynomial.decodeCubic 21 atom0750Coded := by decide +kernel
theorem atom0750Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded) := by
  have h := atom0750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0751 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0751 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0751 = ((g 2) * (g 17) * (g 18)) := by
  norm_num [atom0751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0751_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61939813017600 : Int) atom0751) := by
  rw [SparsePolynomial.eval_scale, eval_atom0751]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0751Coded : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 1))]
theorem atom0751Coded_decode : atom0751 = SparsePolynomial.decodeCubic 21 atom0751Coded := by decide +kernel
theorem atom0751Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) := by
  have h := atom0751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0752 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0752 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0752 = ((g 2) * (g 17) * (g 19)) := by
  norm_num [atom0752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0752_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39050030880000 : Int) atom0752) := by
  rw [SparsePolynomial.eval_scale, eval_atom0752]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0752Coded : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 1))]
theorem atom0752Coded_decode : atom0752 = SparsePolynomial.decodeCubic 21 atom0752Coded := by decide +kernel
theorem atom0752Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded) := by
  have h := atom0752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0753 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0753 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0753 = ((g 2) * (g 17) * (g 20)) := by
  norm_num [atom0753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0753_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49287368592000 : Int) atom0753) := by
  rw [SparsePolynomial.eval_scale, eval_atom0753]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0753Coded : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 1))]
theorem atom0753Coded_decode : atom0753 = SparsePolynomial.decodeCubic 21 atom0753Coded := by decide +kernel
theorem atom0753Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) := by
  have h := atom0753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0754 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0754 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0754 = ((g 2) * (g 18) * (g 18)) := by
  norm_num [atom0754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0754_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20684399500800 : Int) atom0754) := by
  rw [SparsePolynomial.eval_scale, eval_atom0754]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0754Coded : CoefficientMerge.Poly := [(nat_lit 1278, Int.ofNat (nat_lit 1))]
theorem atom0754Coded_decode : atom0754 = SparsePolynomial.decodeCubic 21 atom0754Coded := by decide +kernel
theorem atom0754Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) := by
  have h := atom0754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0755 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0755 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0755 = ((g 2) * (g 18) * (g 19)) := by
  norm_num [atom0755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0755_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25066859529600 : Int) atom0755) := by
  rw [SparsePolynomial.eval_scale, eval_atom0755]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0755Coded : CoefficientMerge.Poly := [(nat_lit 1279, Int.ofNat (nat_lit 1))]
theorem atom0755Coded_decode : atom0755 = SparsePolynomial.decodeCubic 21 atom0755Coded := by decide +kernel
theorem atom0755Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded) := by
  have h := atom0755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0756 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0756 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0756 = ((g 2) * (g 18) * (g 20)) := by
  norm_num [atom0756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0756_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36979573680000 : Int) atom0756) := by
  rw [SparsePolynomial.eval_scale, eval_atom0756]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0756Coded : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 1))]
theorem atom0756Coded_decode : atom0756 = SparsePolynomial.decodeCubic 21 atom0756Coded := by decide +kernel
theorem atom0756Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) := by
  have h := atom0756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0757 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0757 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0757 = ((g 2) * (g 19) * (g 19)) := by
  norm_num [atom0757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0757_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1177160947200 : Int) atom0757) := by
  rw [SparsePolynomial.eval_scale, eval_atom0757]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0757Coded : CoefficientMerge.Poly := [(nat_lit 1300, Int.ofNat (nat_lit 1))]
theorem atom0757Coded_decode : atom0757 = SparsePolynomial.decodeCubic 21 atom0757Coded := by decide +kernel
theorem atom0757Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded) := by
  have h := atom0757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0758 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0758 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0758 = ((g 2) * (g 19) * (g 20)) := by
  norm_num [atom0758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0758_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14227652376000 : Int) atom0758) := by
  rw [SparsePolynomial.eval_scale, eval_atom0758]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0758Coded : CoefficientMerge.Poly := [(nat_lit 1301, Int.ofNat (nat_lit 1))]
theorem atom0758Coded_decode : atom0758 = SparsePolynomial.decodeCubic 21 atom0758Coded := by decide +kernel
theorem atom0758Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) := by
  have h := atom0758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0759 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0759 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0759 = ((g 2) * (g 20) * (g 20)) := by
  norm_num [atom0759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0759_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11225070460800 : Int) atom0759) := by
  rw [SparsePolynomial.eval_scale, eval_atom0759]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0759Coded : CoefficientMerge.Poly := [(nat_lit 1322, Int.ofNat (nat_lit 1))]
theorem atom0759Coded_decode : atom0759 = SparsePolynomial.decodeCubic 21 atom0759Coded := by decide +kernel
theorem atom0759Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) := by
  have h := atom0759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0760 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0760 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0760 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0760_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2137832524800 : Int) atom0760) := by
  rw [SparsePolynomial.eval_scale, eval_atom0760]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0760Coded : CoefficientMerge.Poly := [(nat_lit 1389, Int.ofNat (nat_lit 1))]
theorem atom0760Coded_decode : atom0760 = SparsePolynomial.decodeCubic 21 atom0760Coded := by decide +kernel
theorem atom0760Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded) := by
  have h := atom0760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0761 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0761 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0761 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0761_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5713773004800 : Int) atom0761) := by
  rw [SparsePolynomial.eval_scale, eval_atom0761]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0761Coded : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 1))]
theorem atom0761Coded_decode : atom0761 = SparsePolynomial.decodeCubic 21 atom0761Coded := by decide +kernel
theorem atom0761Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) := by
  have h := atom0761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0762 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0762 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0762 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0762_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6505426397952 : Int) atom0762) := by
  rw [SparsePolynomial.eval_scale, eval_atom0762]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0762Coded : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 1))]
theorem atom0762Coded_decode : atom0762 = SparsePolynomial.decodeCubic 21 atom0762Coded := by decide +kernel
theorem atom0762Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded) := by
  have h := atom0762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0763 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0763 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0763 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0763_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6259026816000 : Int) atom0763) := by
  rw [SparsePolynomial.eval_scale, eval_atom0763]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0763Coded : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 1))]
theorem atom0763Coded_decode : atom0763 = SparsePolynomial.decodeCubic 21 atom0763Coded := by decide +kernel
theorem atom0763Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) := by
  have h := atom0763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0764 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0764 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0764 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0764_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7013098571904 : Int) atom0764) := by
  rw [SparsePolynomial.eval_scale, eval_atom0764]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0764Coded : CoefficientMerge.Poly := [(nat_lit 1393, Int.ofNat (nat_lit 1))]
theorem atom0764Coded_decode : atom0764 = SparsePolynomial.decodeCubic 21 atom0764Coded := by decide +kernel
theorem atom0764Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) := by
  have h := atom0764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0765 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0765 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0765 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0765_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6815549260800 : Int) atom0765) := by
  rw [SparsePolynomial.eval_scale, eval_atom0765]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0765Coded : CoefficientMerge.Poly := [(nat_lit 1394, Int.ofNat (nat_lit 1))]
theorem atom0765Coded_decode : atom0765 = SparsePolynomial.decodeCubic 21 atom0765Coded := by decide +kernel
theorem atom0765Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded) := by
  have h := atom0765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0766 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0766 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0766 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0766_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6543004608000 : Int) atom0766) := by
  rw [SparsePolynomial.eval_scale, eval_atom0766]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0766Coded : CoefficientMerge.Poly := [(nat_lit 1395, Int.ofNat (nat_lit 1))]
theorem atom0766Coded_decode : atom0766 = SparsePolynomial.decodeCubic 21 atom0766Coded := by decide +kernel
theorem atom0766Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) := by
  have h := atom0766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0767 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0767 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0767 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom0767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0767_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6270459955200 : Int) atom0767) := by
  rw [SparsePolynomial.eval_scale, eval_atom0767]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0767Coded : CoefficientMerge.Poly := [(nat_lit 1396, Int.ofNat (nat_lit 1))]
theorem atom0767Coded_decode : atom0767 = SparsePolynomial.decodeCubic 21 atom0767Coded := by decide +kernel
theorem atom0767Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded) := by
  have h := atom0767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0768 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0768 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0768 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0768_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5685991718400 : Int) atom0768) := by
  rw [SparsePolynomial.eval_scale, eval_atom0768]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0768Coded : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 1))]
theorem atom0768Coded_decode : atom0768 = SparsePolynomial.decodeCubic 21 atom0768Coded := by decide +kernel
theorem atom0768Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) := by
  have h := atom0768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0769 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0769 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0769 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom0769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0769_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3051970342400 : Int) atom0769) := by
  rw [SparsePolynomial.eval_scale, eval_atom0769]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0769Coded : CoefficientMerge.Poly := [(nat_lit 1398, Int.ofNat (nat_lit 1))]
theorem atom0769Coded_decode : atom0769 = SparsePolynomial.decodeCubic 21 atom0769Coded := by decide +kernel
theorem atom0769Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) := by
  have h := atom0769_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0769Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0770 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0770 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0770 = ((g 3) * (g 3) * (g 13)) := by
  norm_num [atom0770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0770_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2161027814400 : Int) atom0770) := by
  rw [SparsePolynomial.eval_scale, eval_atom0770]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0770Coded : CoefficientMerge.Poly := [(nat_lit 1399, Int.ofNat (nat_lit 1))]
theorem atom0770Coded_decode : atom0770 = SparsePolynomial.decodeCubic 21 atom0770Coded := by decide +kernel
theorem atom0770Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded) := by
  have h := atom0770_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0770Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0771 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0771 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0771 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom0771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0771_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2147497228800 : Int) atom0771) := by
  rw [SparsePolynomial.eval_scale, eval_atom0771]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0771Coded : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 1))]
theorem atom0771Coded_decode : atom0771 = SparsePolynomial.decodeCubic 21 atom0771Coded := by decide +kernel
theorem atom0771Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) := by
  have h := atom0771_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0771Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0772 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0772 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0772 = ((g 3) * (g 3) * (g 15)) := by
  norm_num [atom0772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0772_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6541071667200 : Int) atom0772) := by
  rw [SparsePolynomial.eval_scale, eval_atom0772]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0772Coded : CoefficientMerge.Poly := [(nat_lit 1401, Int.ofNat (nat_lit 1))]
theorem atom0772Coded_decode : atom0772 = SparsePolynomial.decodeCubic 21 atom0772Coded := by decide +kernel
theorem atom0772Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded) := by
  have h := atom0772_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0772Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0773 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0773 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0773 = ((g 3) * (g 3) * (g 17)) := by
  norm_num [atom0773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0773_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4107293568000 : Int) atom0773) := by
  rw [SparsePolynomial.eval_scale, eval_atom0773]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0773Coded : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 1))]
theorem atom0773Coded_decode : atom0773 = SparsePolynomial.decodeCubic 21 atom0773Coded := by decide +kernel
theorem atom0773Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) := by
  have h := atom0773_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0773Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0774 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0774 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0774 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0774_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5453792467200 : Int) atom0774) := by
  rw [SparsePolynomial.eval_scale, eval_atom0774]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0774Coded : CoefficientMerge.Poly := [(nat_lit 1411, Int.ofNat (nat_lit 1))]
theorem atom0774Coded_decode : atom0774 = SparsePolynomial.decodeCubic 21 atom0774Coded := by decide +kernel
theorem atom0774Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) := by
  have h := atom0774_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0774Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0775 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0775 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0775 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0775_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8897326502400 : Int) atom0775) := by
  rw [SparsePolynomial.eval_scale, eval_atom0775]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0775Coded : CoefficientMerge.Poly := [(nat_lit 1412, Int.ofNat (nat_lit 1))]
theorem atom0775Coded_decode : atom0775 = SparsePolynomial.decodeCubic 21 atom0775Coded := by decide +kernel
theorem atom0775Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded) := by
  have h := atom0775_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0775Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0776 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0776 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0776 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0776_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9046491955200 : Int) atom0776) := by
  rw [SparsePolynomial.eval_scale, eval_atom0776]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0776Coded : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 1))]
theorem atom0776Coded_decode : atom0776 = SparsePolynomial.decodeCubic 21 atom0776Coded := by decide +kernel
theorem atom0776Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) := by
  have h := atom0776_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0776Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0777 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0777 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0777 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0777_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11227298865408 : Int) atom0777) := by
  rw [SparsePolynomial.eval_scale, eval_atom0777]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0777Coded : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 1))]
theorem atom0777Coded_decode : atom0777 = SparsePolynomial.decodeCubic 21 atom0777Coded := by decide +kernel
theorem atom0777Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded) := by
  have h := atom0777_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0777Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0778 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0778 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0778 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0778_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11504863641600 : Int) atom0778) := by
  rw [SparsePolynomial.eval_scale, eval_atom0778]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0778Coded : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 1))]
theorem atom0778Coded_decode : atom0778 = SparsePolynomial.decodeCubic 21 atom0778Coded := by decide +kernel
theorem atom0778Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) := by
  have h := atom0778_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0778Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0779 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0779 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0779 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0779_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11632437734400 : Int) atom0779) := by
  rw [SparsePolynomial.eval_scale, eval_atom0779]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0779Coded : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 1))]
theorem atom0779Coded_decode : atom0779 = SparsePolynomial.decodeCubic 21 atom0779Coded := by decide +kernel
theorem atom0779Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) := by
  have h := atom0779_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0779Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0780 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0780 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0780 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0780_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11760011827200 : Int) atom0780) := by
  rw [SparsePolynomial.eval_scale, eval_atom0780]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0780Coded : CoefficientMerge.Poly := [(nat_lit 1417, Int.ofNat (nat_lit 1))]
theorem atom0780Coded_decode : atom0780 = SparsePolynomial.decodeCubic 21 atom0780Coded := by decide +kernel
theorem atom0780Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded) := by
  have h := atom0780_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0780Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0781 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0781 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0781 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0781_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11263738752000 : Int) atom0781) := by
  rw [SparsePolynomial.eval_scale, eval_atom0781]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0781Coded : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 1))]
theorem atom0781Coded_decode : atom0781 = SparsePolynomial.decodeCubic 21 atom0781Coded := by decide +kernel
theorem atom0781Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) := by
  have h := atom0781_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0781Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0782 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0782 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0782 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0782_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7479371244800 : Int) atom0782) := by
  rw [SparsePolynomial.eval_scale, eval_atom0782]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0782Coded : CoefficientMerge.Poly := [(nat_lit 1419, Int.ofNat (nat_lit 1))]
theorem atom0782Coded_decode : atom0782 = SparsePolynomial.decodeCubic 21 atom0782Coded := by decide +kernel
theorem atom0782Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded) := by
  have h := atom0782_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0782Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0783 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0783 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0783 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0783_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7015608633600 : Int) atom0783) := by
  rw [SparsePolynomial.eval_scale, eval_atom0783]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0783Coded : CoefficientMerge.Poly := [(nat_lit 1420, Int.ofNat (nat_lit 1))]
theorem atom0783Coded_decode : atom0783 = SparsePolynomial.decodeCubic 21 atom0783Coded := by decide +kernel
theorem atom0783Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) := by
  have h := atom0783_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0783Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0784 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0784 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0784 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0784_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7429257964800 : Int) atom0784) := by
  rw [SparsePolynomial.eval_scale, eval_atom0784]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0784Coded : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 1))]
theorem atom0784Coded_decode : atom0784 = SparsePolynomial.decodeCubic 21 atom0784Coded := by decide +kernel
theorem atom0784Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) := by
  have h := atom0784_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0784Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0785 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0785 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0785 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom0785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0785_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15664552243200 : Int) atom0785) := by
  rw [SparsePolynomial.eval_scale, eval_atom0785]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0785Coded : CoefficientMerge.Poly := [(nat_lit 1422, Int.ofNat (nat_lit 1))]
theorem atom0785Coded_decode : atom0785 = SparsePolynomial.decodeCubic 21 atom0785Coded := by decide +kernel
theorem atom0785Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded) := by
  have h := atom0785_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0785Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0786 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0786 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0786 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom0786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0786_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6941794456800 : Int) atom0786) := by
  rw [SparsePolynomial.eval_scale, eval_atom0786]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0786Coded : CoefficientMerge.Poly := [(nat_lit 1423, Int.ofNat (nat_lit 1))]
theorem atom0786Coded_decode : atom0786 = SparsePolynomial.decodeCubic 21 atom0786Coded := by decide +kernel
theorem atom0786Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) := by
  have h := atom0786_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0786Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0787 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0787 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0787 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom0787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0787_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12142322841600 : Int) atom0787) := by
  rw [SparsePolynomial.eval_scale, eval_atom0787]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0787Coded : CoefficientMerge.Poly := [(nat_lit 1424, Int.ofNat (nat_lit 1))]
theorem atom0787Coded_decode : atom0787 = SparsePolynomial.decodeCubic 21 atom0787Coded := by decide +kernel
theorem atom0787Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded) := by
  have h := atom0787_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0787Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0788 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0788 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0788 = ((g 3) * (g 4) * (g 18)) := by
  norm_num [atom0788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0788_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9407502064800 : Int) atom0788) := by
  rw [SparsePolynomial.eval_scale, eval_atom0788]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0788Coded : CoefficientMerge.Poly := [(nat_lit 1425, Int.ofNat (nat_lit 1))]
theorem atom0788Coded_decode : atom0788 = SparsePolynomial.decodeCubic 21 atom0788Coded := by decide +kernel
theorem atom0788Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) := by
  have h := atom0788_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0788Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0789 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0789 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0789 = ((g 3) * (g 4) * (g 19)) := by
  norm_num [atom0789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0789_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10908913831200 : Int) atom0789) := by
  rw [SparsePolynomial.eval_scale, eval_atom0789]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0789Coded : CoefficientMerge.Poly := [(nat_lit 1426, Int.ofNat (nat_lit 1))]
theorem atom0789Coded_decode : atom0789 = SparsePolynomial.decodeCubic 21 atom0789Coded := by decide +kernel
theorem atom0789Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) := by
  have h := atom0789_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0789Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0790 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0790 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0790 = ((g 3) * (g 4) * (g 20)) := by
  norm_num [atom0790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0790_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12410325597600 : Int) atom0790) := by
  rw [SparsePolynomial.eval_scale, eval_atom0790]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0790Coded : CoefficientMerge.Poly := [(nat_lit 1427, Int.ofNat (nat_lit 1))]
theorem atom0790Coded_decode : atom0790 = SparsePolynomial.decodeCubic 21 atom0790Coded := by decide +kernel
theorem atom0790Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded) := by
  have h := atom0790_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0790Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0791 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0791 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0791 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0791_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8572592448000 : Int) atom0791) := by
  rw [SparsePolynomial.eval_scale, eval_atom0791]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0791Coded : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 1))]
theorem atom0791Coded_decode : atom0791 = SparsePolynomial.decodeCubic 21 atom0791Coded := by decide +kernel
theorem atom0791Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) := by
  have h := atom0791_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0791Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0792 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0792 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0792 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0792_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15532145798400 : Int) atom0792) := by
  rw [SparsePolynomial.eval_scale, eval_atom0792]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0792Coded : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 1))]
theorem atom0792Coded_decode : atom0792 = SparsePolynomial.decodeCubic 21 atom0792Coded := by decide +kernel
theorem atom0792Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded) := by
  have h := atom0792_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0792Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0793 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0793 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0793 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0793_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12347854101504 : Int) atom0793) := by
  rw [SparsePolynomial.eval_scale, eval_atom0793]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0793Coded : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 1))]
theorem atom0793Coded_decode : atom0793 = SparsePolynomial.decodeCubic 21 atom0793Coded := by decide +kernel
theorem atom0793Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) := by
  have h := atom0793_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0793Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0794 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0794 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0794 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0794_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12361384687104 : Int) atom0794) := by
  rw [SparsePolynomial.eval_scale, eval_atom0794]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0794Coded : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 1))]
theorem atom0794Coded_decode : atom0794 = SparsePolynomial.decodeCubic 21 atom0794Coded := by decide +kernel
theorem atom0794Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) := by
  have h := atom0794_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0794Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0795 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0795 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0795 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0795_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13891307330304 : Int) atom0795) := by
  rw [SparsePolynomial.eval_scale, eval_atom0795]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0795Coded : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 1))]
theorem atom0795Coded_decode : atom0795 = SparsePolynomial.decodeCubic 21 atom0795Coded := by decide +kernel
theorem atom0795Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded) := by
  have h := atom0795_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0795Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0796 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0796 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0796 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0796_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13961859669504 : Int) atom0796) := by
  rw [SparsePolynomial.eval_scale, eval_atom0796]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0796Coded : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 1))]
theorem atom0796Coded_decode : atom0796 = SparsePolynomial.decodeCubic 21 atom0796Coded := by decide +kernel
theorem atom0796Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) := by
  have h := atom0796_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0796Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0797 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0797 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0797 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0797_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14138249992704 : Int) atom0797) := by
  rw [SparsePolynomial.eval_scale, eval_atom0797]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0797Coded : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 1))]
theorem atom0797Coded_decode : atom0797 = SparsePolynomial.decodeCubic 21 atom0797Coded := by decide +kernel
theorem atom0797Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded) := by
  have h := atom0797_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0797Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0798 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0798 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0798 = ((g 3) * (g 5) * (g 12)) := by
  norm_num [atom0798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0798_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11604495183104 : Int) atom0798) := by
  rw [SparsePolynomial.eval_scale, eval_atom0798]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0798Coded : CoefficientMerge.Poly := [(nat_lit 1440, Int.ofNat (nat_lit 1))]
theorem atom0798Coded_decode : atom0798 = SparsePolynomial.decodeCubic 21 atom0798Coded := by decide +kernel
theorem atom0798Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) := by
  have h := atom0798_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0798Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0799 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0799 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0799 = ((g 3) * (g 5) * (g 13)) := by
  norm_num [atom0799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0799_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11137833160704 : Int) atom0799) := by
  rw [SparsePolynomial.eval_scale, eval_atom0799]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0799Coded : CoefficientMerge.Poly := [(nat_lit 1441, Int.ofNat (nat_lit 1))]
theorem atom0799Coded_decode : atom0799 = SparsePolynomial.decodeCubic 21 atom0799Coded := by decide +kernel
theorem atom0799Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) := by
  have h := atom0799_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0799Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0800 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0800 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0800 = ((g 3) * (g 5) * (g 14)) := by
  norm_num [atom0800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0800_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11810496559104 : Int) atom0800) := by
  rw [SparsePolynomial.eval_scale, eval_atom0800]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0800Coded : CoefficientMerge.Poly := [(nat_lit 1442, Int.ofNat (nat_lit 1))]
theorem atom0800Coded_decode : atom0800 = SparsePolynomial.decodeCubic 21 atom0800Coded := by decide +kernel
theorem atom0800Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded) := by
  have h := atom0800_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0800Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0801 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0801 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0801 = ((g 3) * (g 5) * (g 15)) := by
  norm_num [atom0801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0801_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21229717077504 : Int) atom0801) := by
  rw [SparsePolynomial.eval_scale, eval_atom0801]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0801Coded : CoefficientMerge.Poly := [(nat_lit 1443, Int.ofNat (nat_lit 1))]
theorem atom0801Coded_decode : atom0801 = SparsePolynomial.decodeCubic 21 atom0801Coded := by decide +kernel
theorem atom0801Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) := by
  have h := atom0801_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0801Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0802 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0802 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0802 = ((g 3) * (g 5) * (g 16)) := by
  norm_num [atom0802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0802_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12805392234240 : Int) atom0802) := by
  rw [SparsePolynomial.eval_scale, eval_atom0802]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0802Coded : CoefficientMerge.Poly := [(nat_lit 1444, Int.ofNat (nat_lit 1))]
theorem atom0802Coded_decode : atom0802 = SparsePolynomial.decodeCubic 21 atom0802Coded := by decide +kernel
theorem atom0802Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded) := by
  have h := atom0802_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0802Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0803 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0803 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0803 = ((g 3) * (g 5) * (g 17)) := by
  norm_num [atom0803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0803_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19052814472704 : Int) atom0803) := by
  rw [SparsePolynomial.eval_scale, eval_atom0803]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0803Coded : CoefficientMerge.Poly := [(nat_lit 1445, Int.ofNat (nat_lit 1))]
theorem atom0803Coded_decode : atom0803 = SparsePolynomial.decodeCubic 21 atom0803Coded := by decide +kernel
theorem atom0803Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) := by
  have h := atom0803_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0803Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0804 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0804 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0804 = ((g 3) * (g 5) * (g 18)) := by
  norm_num [atom0804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0804_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17717790074112 : Int) atom0804) := by
  rw [SparsePolynomial.eval_scale, eval_atom0804]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0804Coded : CoefficientMerge.Poly := [(nat_lit 1446, Int.ofNat (nat_lit 1))]
theorem atom0804Coded_decode : atom0804 = SparsePolynomial.decodeCubic 21 atom0804Coded := by decide +kernel
theorem atom0804Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) := by
  have h := atom0804_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0804Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0805 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0805 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0805 = ((g 3) * (g 5) * (g 19)) := by
  norm_num [atom0805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0805_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20763990639360 : Int) atom0805) := by
  rw [SparsePolynomial.eval_scale, eval_atom0805]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0805Coded : CoefficientMerge.Poly := [(nat_lit 1447, Int.ofNat (nat_lit 1))]
theorem atom0805Coded_decode : atom0805 = SparsePolynomial.decodeCubic 21 atom0805Coded := by decide +kernel
theorem atom0805Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded) := by
  have h := atom0805_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0805Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0806 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0806 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0806 = ((g 3) * (g 5) * (g 20)) := by
  norm_num [atom0806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0806_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23810191204608 : Int) atom0806) := by
  rw [SparsePolynomial.eval_scale, eval_atom0806]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0806Coded : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 1))]
theorem atom0806Coded_decode : atom0806 = SparsePolynomial.decodeCubic 21 atom0806Coded := by decide +kernel
theorem atom0806Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) := by
  have h := atom0806_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0806Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0807 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0807 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0807 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0807_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12088611763200 : Int) atom0807) := by
  rw [SparsePolynomial.eval_scale, eval_atom0807]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0807Coded : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 1))]
theorem atom0807Coded_decode : atom0807 = SparsePolynomial.decodeCubic 21 atom0807Coded := by decide +kernel
theorem atom0807Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded) := by
  have h := atom0807_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0807Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0808 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0808 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0808 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0808_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21174628264704 : Int) atom0808) := by
  rw [SparsePolynomial.eval_scale, eval_atom0808]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0808Coded : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 1))]
theorem atom0808Coded_decode : atom0808 = SparsePolynomial.decodeCubic 21 atom0808Coded := by decide +kernel
theorem atom0808Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) := by
  have h := atom0808_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0808Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0809 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0809 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0809 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0809, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0809_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391473769600 : Int) atom0809) := by
  rw [SparsePolynomial.eval_scale, eval_atom0809]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0809Coded : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 1))]
theorem atom0809Coded_decode : atom0809 = SparsePolynomial.decodeCubic 21 atom0809Coded := by decide +kernel
theorem atom0809Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) := by
  have h := atom0809_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0809Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0810 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0810 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0810 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0810, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0810_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14851113177600 : Int) atom0810) := by
  rw [SparsePolynomial.eval_scale, eval_atom0810]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0810Coded : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 1))]
theorem atom0810Coded_decode : atom0810 = SparsePolynomial.decodeCubic 21 atom0810Coded := by decide +kernel
theorem atom0810Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded) := by
  have h := atom0810_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0810Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0811 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0811 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0811 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0811, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0811_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15271527801600 : Int) atom0811) := by
  rw [SparsePolynomial.eval_scale, eval_atom0811]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0811Coded : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 1))]
theorem atom0811Coded_decode : atom0811 = SparsePolynomial.decodeCubic 21 atom0811Coded := by decide +kernel
theorem atom0811Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) := by
  have h := atom0811_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0811Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0812 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0812 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0812 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0812, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0812_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15121004774400 : Int) atom0812) := by
  rw [SparsePolynomial.eval_scale, eval_atom0812]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0812Coded : CoefficientMerge.Poly := [(nat_lit 1460, Int.ofNat (nat_lit 1))]
theorem atom0812Coded_decode : atom0812 = SparsePolynomial.decodeCubic 21 atom0812Coded := by decide +kernel
theorem atom0812Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded) := by
  have h := atom0812_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0812Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0813 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0813 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0813 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom0813, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0813_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13264025600000 : Int) atom0813) := by
  rw [SparsePolynomial.eval_scale, eval_atom0813]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0813Coded : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 1))]
theorem atom0813Coded_decode : atom0813 = SparsePolynomial.decodeCubic 21 atom0813Coded := by decide +kernel
theorem atom0813Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) := by
  have h := atom0813_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0813Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0814 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0814 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0814 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom0814, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0814_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13150125273600 : Int) atom0814) := by
  rw [SparsePolynomial.eval_scale, eval_atom0814]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0814Coded : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 1))]
theorem atom0814Coded_decode : atom0814 = SparsePolynomial.decodeCubic 21 atom0814Coded := by decide +kernel
theorem atom0814Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) := by
  have h := atom0814_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0814Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0815 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0815 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0815 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom0815, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0815_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13913636889600 : Int) atom0815) := by
  rw [SparsePolynomial.eval_scale, eval_atom0815]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0815Coded : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 1))]
theorem atom0815Coded_decode : atom0815 = SparsePolynomial.decodeCubic 21 atom0815Coded := by decide +kernel
theorem atom0815Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded) := by
  have h := atom0815_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0815Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block011 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560)), (nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600)), (nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800)), (nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400)), (nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200)), (nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304)), (nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360)), (nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
def block011_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600))]
theorem block011_data_flat000_step : block011_data_flat000 = (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) := by decide +kernel
theorem block011_data_flat000_original : block011_data_flat000 = (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) := by
  rw [block011_data_flat000_step]
def block011_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1195, Int.ofNat (nat_lit 39762525196800))]
theorem block011_data_flat001_step : block011_data_flat001 = (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded) := by decide +kernel
theorem block011_data_flat001_original : block011_data_flat001 = (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded) := by
  rw [block011_data_flat001_step]
def block011_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800))]
theorem block011_data_flat002_step : block011_data_flat002 = (CoefficientMerge.fastMerge block011_data_flat000 block011_data_flat001) := by decide +kernel
theorem block011_data_flat002_original : block011_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) := by
  rw [block011_data_flat002_step, block011_data_flat000_original, block011_data_flat001_original]
def block011_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1196, Int.ofNat (nat_lit 56627433676800))]
theorem block011_data_flat003_step : block011_data_flat003 = (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) := by decide +kernel
theorem block011_data_flat003_original : block011_data_flat003 = (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) := by
  rw [block011_data_flat003_step]
def block011_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1212, Int.ofNat (nat_lit 33575181696000))]
theorem block011_data_flat004_step : block011_data_flat004 = (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) := by decide +kernel
theorem block011_data_flat004_original : block011_data_flat004 = (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) := by
  rw [block011_data_flat004_step]
def block011_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1213, Int.ofNat (nat_lit 55106209267200))]
theorem block011_data_flat005_step : block011_data_flat005 = (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded) := by decide +kernel
theorem block011_data_flat005_original : block011_data_flat005 = (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded) := by
  rw [block011_data_flat005_step]
def block011_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200))]
theorem block011_data_flat006_step : block011_data_flat006 = (CoefficientMerge.fastMerge block011_data_flat004 block011_data_flat005) := by decide +kernel
theorem block011_data_flat006_original : block011_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)) := by
  rw [block011_data_flat006_step, block011_data_flat004_original, block011_data_flat005_original]
def block011_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200))]
theorem block011_data_flat007_step : block011_data_flat007 = (CoefficientMerge.fastMerge block011_data_flat003 block011_data_flat006) := by decide +kernel
theorem block011_data_flat007_original : block011_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded))) := by
  rw [block011_data_flat007_step, block011_data_flat003_original, block011_data_flat006_original]
def block011_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200))]
theorem block011_data_flat008_step : block011_data_flat008 = (CoefficientMerge.fastMerge block011_data_flat002 block011_data_flat007) := by decide +kernel
theorem block011_data_flat008_original : block011_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) := by
  rw [block011_data_flat008_step, block011_data_flat002_original, block011_data_flat007_original]
def block011_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1214, Int.ofNat (nat_lit 75090472934400))]
theorem block011_data_flat009_step : block011_data_flat009 = (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) := by decide +kernel
theorem block011_data_flat009_original : block011_data_flat009 = (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) := by
  rw [block011_data_flat009_step]
def block011_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1215, Int.ofNat (nat_lit 65114976729600))]
theorem block011_data_flat010_step : block011_data_flat010 = (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded) := by decide +kernel
theorem block011_data_flat010_original : block011_data_flat010 = (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded) := by
  rw [block011_data_flat010_step]
def block011_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600))]
theorem block011_data_flat011_step : block011_data_flat011 = (CoefficientMerge.fastMerge block011_data_flat009 block011_data_flat010) := by decide +kernel
theorem block011_data_flat011_original : block011_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) := by
  rw [block011_data_flat011_step, block011_data_flat009_original, block011_data_flat010_original]
def block011_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1216, Int.ofNat (nat_lit 39869803411200))]
theorem block011_data_flat012_step : block011_data_flat012 = (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) := by decide +kernel
theorem block011_data_flat012_original : block011_data_flat012 = (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) := by
  rw [block011_data_flat012_step]
def block011_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1217, Int.ofNat (nat_lit 60710287881600))]
theorem block011_data_flat013_step : block011_data_flat013 = (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) := by decide +kernel
theorem block011_data_flat013_original : block011_data_flat013 = (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) := by
  rw [block011_data_flat013_step]
def block011_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1234, Int.ofNat (nat_lit 22698910402560))]
theorem block011_data_flat014_step : block011_data_flat014 = (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded) := by decide +kernel
theorem block011_data_flat014_original : block011_data_flat014 = (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded) := by
  rw [block011_data_flat014_step]
def block011_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560))]
theorem block011_data_flat015_step : block011_data_flat015 = (CoefficientMerge.fastMerge block011_data_flat013 block011_data_flat014) := by decide +kernel
theorem block011_data_flat015_original : block011_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded)) := by
  rw [block011_data_flat015_step, block011_data_flat013_original, block011_data_flat014_original]
def block011_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560))]
theorem block011_data_flat016_step : block011_data_flat016 = (CoefficientMerge.fastMerge block011_data_flat012 block011_data_flat015) := by decide +kernel
theorem block011_data_flat016_original : block011_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))) := by
  rw [block011_data_flat016_step, block011_data_flat012_original, block011_data_flat015_original]
def block011_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560))]
theorem block011_data_flat017_step : block011_data_flat017 = (CoefficientMerge.fastMerge block011_data_flat011 block011_data_flat016) := by decide +kernel
theorem block011_data_flat017_original : block011_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded)))) := by
  rw [block011_data_flat017_step, block011_data_flat011_original, block011_data_flat016_original]
def block011_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560))]
theorem block011_data_flat018_step : block011_data_flat018 = (CoefficientMerge.fastMerge block011_data_flat008 block011_data_flat017) := by decide +kernel
theorem block011_data_flat018_original : block011_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) := by
  rw [block011_data_flat018_step, block011_data_flat008_original, block011_data_flat017_original]
def block011_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 61504901337600))]
theorem block011_data_flat019_step : block011_data_flat019 = (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) := by decide +kernel
theorem block011_data_flat019_original : block011_data_flat019 = (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) := by
  rw [block011_data_flat019_step]
def block011_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1236, Int.ofNat (nat_lit 60041007129600))]
theorem block011_data_flat020_step : block011_data_flat020 = (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded) := by decide +kernel
theorem block011_data_flat020_original : block011_data_flat020 = (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded) := by
  rw [block011_data_flat020_step]
def block011_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600))]
theorem block011_data_flat021_step : block011_data_flat021 = (CoefficientMerge.fastMerge block011_data_flat019 block011_data_flat020) := by decide +kernel
theorem block011_data_flat021_original : block011_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) := by
  rw [block011_data_flat021_step, block011_data_flat019_original, block011_data_flat020_original]
def block011_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 39977081625600))]
theorem block011_data_flat022_step : block011_data_flat022 = (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) := by decide +kernel
theorem block011_data_flat022_original : block011_data_flat022 = (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) := by
  rw [block011_data_flat022_step]
def block011_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 47368164009600))]
theorem block011_data_flat023_step : block011_data_flat023 = (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) := by decide +kernel
theorem block011_data_flat023_original : block011_data_flat023 = (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) := by
  rw [block011_data_flat023_step]
def block011_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1256, Int.ofNat (nat_lit 39973873766400))]
theorem block011_data_flat024_step : block011_data_flat024 = (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded) := by decide +kernel
theorem block011_data_flat024_original : block011_data_flat024 = (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded) := by
  rw [block011_data_flat024_step]
def block011_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400))]
theorem block011_data_flat025_step : block011_data_flat025 = (CoefficientMerge.fastMerge block011_data_flat023 block011_data_flat024) := by decide +kernel
theorem block011_data_flat025_original : block011_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)) := by
  rw [block011_data_flat025_step, block011_data_flat023_original, block011_data_flat024_original]
def block011_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400))]
theorem block011_data_flat026_step : block011_data_flat026 = (CoefficientMerge.fastMerge block011_data_flat022 block011_data_flat025) := by decide +kernel
theorem block011_data_flat026_original : block011_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded))) := by
  rw [block011_data_flat026_step, block011_data_flat022_original, block011_data_flat025_original]
def block011_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400))]
theorem block011_data_flat027_step : block011_data_flat027 = (CoefficientMerge.fastMerge block011_data_flat021 block011_data_flat026) := by decide +kernel
theorem block011_data_flat027_original : block011_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) := by
  rw [block011_data_flat027_step, block011_data_flat021_original, block011_data_flat026_original]
def block011_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 61939813017600))]
theorem block011_data_flat028_step : block011_data_flat028 = (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) := by decide +kernel
theorem block011_data_flat028_original : block011_data_flat028 = (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) := by
  rw [block011_data_flat028_step]
def block011_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 39050030880000))]
theorem block011_data_flat029_step : block011_data_flat029 = (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded) := by decide +kernel
theorem block011_data_flat029_original : block011_data_flat029 = (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded) := by
  rw [block011_data_flat029_step]
def block011_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000))]
theorem block011_data_flat030_step : block011_data_flat030 = (CoefficientMerge.fastMerge block011_data_flat028 block011_data_flat029) := by decide +kernel
theorem block011_data_flat030_original : block011_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) := by
  rw [block011_data_flat030_step, block011_data_flat028_original, block011_data_flat029_original]
def block011_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 49287368592000))]
theorem block011_data_flat031_step : block011_data_flat031 = (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) := by decide +kernel
theorem block011_data_flat031_original : block011_data_flat031 = (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) := by
  rw [block011_data_flat031_step]
def block011_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1278, Int.ofNat (nat_lit 20684399500800))]
theorem block011_data_flat032_step : block011_data_flat032 = (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) := by decide +kernel
theorem block011_data_flat032_original : block011_data_flat032 = (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) := by
  rw [block011_data_flat032_step]
def block011_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat033_step : block011_data_flat033 = (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded) := by decide +kernel
theorem block011_data_flat033_original : block011_data_flat033 = (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded) := by
  rw [block011_data_flat033_step]
def block011_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat034_step : block011_data_flat034 = (CoefficientMerge.fastMerge block011_data_flat032 block011_data_flat033) := by decide +kernel
theorem block011_data_flat034_original : block011_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)) := by
  rw [block011_data_flat034_step, block011_data_flat032_original, block011_data_flat033_original]
def block011_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat035_step : block011_data_flat035 = (CoefficientMerge.fastMerge block011_data_flat031 block011_data_flat034) := by decide +kernel
theorem block011_data_flat035_original : block011_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded))) := by
  rw [block011_data_flat035_step, block011_data_flat031_original, block011_data_flat034_original]
def block011_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat036_step : block011_data_flat036 = (CoefficientMerge.fastMerge block011_data_flat030 block011_data_flat035) := by decide +kernel
theorem block011_data_flat036_original : block011_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))) := by
  rw [block011_data_flat036_step, block011_data_flat030_original, block011_data_flat035_original]
def block011_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat037_step : block011_data_flat037 = (CoefficientMerge.fastMerge block011_data_flat027 block011_data_flat036) := by decide +kernel
theorem block011_data_flat037_original : block011_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded))))) := by
  rw [block011_data_flat037_step, block011_data_flat027_original, block011_data_flat036_original]
def block011_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560)), (nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600))]
theorem block011_data_flat038_step : block011_data_flat038 = (CoefficientMerge.fastMerge block011_data_flat018 block011_data_flat037) := by decide +kernel
theorem block011_data_flat038_original : block011_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))))) := by
  rw [block011_data_flat038_step, block011_data_flat018_original, block011_data_flat037_original]
def block011_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 36979573680000))]
theorem block011_data_flat039_step : block011_data_flat039 = (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) := by decide +kernel
theorem block011_data_flat039_original : block011_data_flat039 = (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) := by
  rw [block011_data_flat039_step]
def block011_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1300, Int.ofNat (nat_lit 1177160947200))]
theorem block011_data_flat040_step : block011_data_flat040 = (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded) := by decide +kernel
theorem block011_data_flat040_original : block011_data_flat040 = (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded) := by
  rw [block011_data_flat040_step]
def block011_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200))]
theorem block011_data_flat041_step : block011_data_flat041 = (CoefficientMerge.fastMerge block011_data_flat039 block011_data_flat040) := by decide +kernel
theorem block011_data_flat041_original : block011_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) := by
  rw [block011_data_flat041_step, block011_data_flat039_original, block011_data_flat040_original]
def block011_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1301, Int.ofNat (nat_lit 14227652376000))]
theorem block011_data_flat042_step : block011_data_flat042 = (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) := by decide +kernel
theorem block011_data_flat042_original : block011_data_flat042 = (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) := by
  rw [block011_data_flat042_step]
def block011_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1322, Int.ofNat (nat_lit 11225070460800))]
theorem block011_data_flat043_step : block011_data_flat043 = (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) := by decide +kernel
theorem block011_data_flat043_original : block011_data_flat043 = (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) := by
  rw [block011_data_flat043_step]
def block011_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1389, Int.ofNat (nat_lit 2137832524800))]
theorem block011_data_flat044_step : block011_data_flat044 = (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded) := by decide +kernel
theorem block011_data_flat044_original : block011_data_flat044 = (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded) := by
  rw [block011_data_flat044_step]
def block011_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800))]
theorem block011_data_flat045_step : block011_data_flat045 = (CoefficientMerge.fastMerge block011_data_flat043 block011_data_flat044) := by decide +kernel
theorem block011_data_flat045_original : block011_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)) := by
  rw [block011_data_flat045_step, block011_data_flat043_original, block011_data_flat044_original]
def block011_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800))]
theorem block011_data_flat046_step : block011_data_flat046 = (CoefficientMerge.fastMerge block011_data_flat042 block011_data_flat045) := by decide +kernel
theorem block011_data_flat046_original : block011_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded))) := by
  rw [block011_data_flat046_step, block011_data_flat042_original, block011_data_flat045_original]
def block011_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800))]
theorem block011_data_flat047_step : block011_data_flat047 = (CoefficientMerge.fastMerge block011_data_flat041 block011_data_flat046) := by decide +kernel
theorem block011_data_flat047_original : block011_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) := by
  rw [block011_data_flat047_step, block011_data_flat041_original, block011_data_flat046_original]
def block011_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 5713773004800))]
theorem block011_data_flat048_step : block011_data_flat048 = (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) := by decide +kernel
theorem block011_data_flat048_original : block011_data_flat048 = (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) := by
  rw [block011_data_flat048_step]
def block011_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 6505426397952))]
theorem block011_data_flat049_step : block011_data_flat049 = (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded) := by decide +kernel
theorem block011_data_flat049_original : block011_data_flat049 = (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded) := by
  rw [block011_data_flat049_step]
def block011_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952))]
theorem block011_data_flat050_step : block011_data_flat050 = (CoefficientMerge.fastMerge block011_data_flat048 block011_data_flat049) := by decide +kernel
theorem block011_data_flat050_original : block011_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) := by
  rw [block011_data_flat050_step, block011_data_flat048_original, block011_data_flat049_original]
def block011_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 6259026816000))]
theorem block011_data_flat051_step : block011_data_flat051 = (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) := by decide +kernel
theorem block011_data_flat051_original : block011_data_flat051 = (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) := by
  rw [block011_data_flat051_step]
def block011_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1393, Int.ofNat (nat_lit 7013098571904))]
theorem block011_data_flat052_step : block011_data_flat052 = (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) := by decide +kernel
theorem block011_data_flat052_original : block011_data_flat052 = (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) := by
  rw [block011_data_flat052_step]
def block011_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1394, Int.ofNat (nat_lit 6815549260800))]
theorem block011_data_flat053_step : block011_data_flat053 = (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded) := by decide +kernel
theorem block011_data_flat053_original : block011_data_flat053 = (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded) := by
  rw [block011_data_flat053_step]
def block011_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800))]
theorem block011_data_flat054_step : block011_data_flat054 = (CoefficientMerge.fastMerge block011_data_flat052 block011_data_flat053) := by decide +kernel
theorem block011_data_flat054_original : block011_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded)) := by
  rw [block011_data_flat054_step, block011_data_flat052_original, block011_data_flat053_original]
def block011_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800))]
theorem block011_data_flat055_step : block011_data_flat055 = (CoefficientMerge.fastMerge block011_data_flat051 block011_data_flat054) := by decide +kernel
theorem block011_data_flat055_original : block011_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))) := by
  rw [block011_data_flat055_step, block011_data_flat051_original, block011_data_flat054_original]
def block011_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800))]
theorem block011_data_flat056_step : block011_data_flat056 = (CoefficientMerge.fastMerge block011_data_flat050 block011_data_flat055) := by decide +kernel
theorem block011_data_flat056_original : block011_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded)))) := by
  rw [block011_data_flat056_step, block011_data_flat050_original, block011_data_flat055_original]
def block011_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800))]
theorem block011_data_flat057_step : block011_data_flat057 = (CoefficientMerge.fastMerge block011_data_flat047 block011_data_flat056) := by decide +kernel
theorem block011_data_flat057_original : block011_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) := by
  rw [block011_data_flat057_step, block011_data_flat047_original, block011_data_flat056_original]
def block011_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1395, Int.ofNat (nat_lit 6543004608000))]
theorem block011_data_flat058_step : block011_data_flat058 = (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) := by decide +kernel
theorem block011_data_flat058_original : block011_data_flat058 = (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) := by
  rw [block011_data_flat058_step]
def block011_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1396, Int.ofNat (nat_lit 6270459955200))]
theorem block011_data_flat059_step : block011_data_flat059 = (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded) := by decide +kernel
theorem block011_data_flat059_original : block011_data_flat059 = (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded) := by
  rw [block011_data_flat059_step]
def block011_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200))]
theorem block011_data_flat060_step : block011_data_flat060 = (CoefficientMerge.fastMerge block011_data_flat058 block011_data_flat059) := by decide +kernel
theorem block011_data_flat060_original : block011_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) := by
  rw [block011_data_flat060_step, block011_data_flat058_original, block011_data_flat059_original]
def block011_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 5685991718400))]
theorem block011_data_flat061_step : block011_data_flat061 = (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) := by decide +kernel
theorem block011_data_flat061_original : block011_data_flat061 = (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) := by
  rw [block011_data_flat061_step]
def block011_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1398, Int.ofNat (nat_lit 3051970342400))]
theorem block011_data_flat062_step : block011_data_flat062 = (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) := by decide +kernel
theorem block011_data_flat062_original : block011_data_flat062 = (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) := by
  rw [block011_data_flat062_step]
def block011_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1399, Int.ofNat (nat_lit 2161027814400))]
theorem block011_data_flat063_step : block011_data_flat063 = (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded) := by decide +kernel
theorem block011_data_flat063_original : block011_data_flat063 = (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded) := by
  rw [block011_data_flat063_step]
def block011_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400))]
theorem block011_data_flat064_step : block011_data_flat064 = (CoefficientMerge.fastMerge block011_data_flat062 block011_data_flat063) := by decide +kernel
theorem block011_data_flat064_original : block011_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)) := by
  rw [block011_data_flat064_step, block011_data_flat062_original, block011_data_flat063_original]
def block011_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400))]
theorem block011_data_flat065_step : block011_data_flat065 = (CoefficientMerge.fastMerge block011_data_flat061 block011_data_flat064) := by decide +kernel
theorem block011_data_flat065_original : block011_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded))) := by
  rw [block011_data_flat065_step, block011_data_flat061_original, block011_data_flat064_original]
def block011_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400))]
theorem block011_data_flat066_step : block011_data_flat066 = (CoefficientMerge.fastMerge block011_data_flat060 block011_data_flat065) := by decide +kernel
theorem block011_data_flat066_original : block011_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) := by
  rw [block011_data_flat066_step, block011_data_flat060_original, block011_data_flat065_original]
def block011_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 2147497228800))]
theorem block011_data_flat067_step : block011_data_flat067 = (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) := by decide +kernel
theorem block011_data_flat067_original : block011_data_flat067 = (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) := by
  rw [block011_data_flat067_step]
def block011_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1401, Int.ofNat (nat_lit 6541071667200))]
theorem block011_data_flat068_step : block011_data_flat068 = (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded) := by decide +kernel
theorem block011_data_flat068_original : block011_data_flat068 = (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded) := by
  rw [block011_data_flat068_step]
def block011_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200))]
theorem block011_data_flat069_step : block011_data_flat069 = (CoefficientMerge.fastMerge block011_data_flat067 block011_data_flat068) := by decide +kernel
theorem block011_data_flat069_original : block011_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) := by
  rw [block011_data_flat069_step, block011_data_flat067_original, block011_data_flat068_original]
def block011_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 4107293568000))]
theorem block011_data_flat070_step : block011_data_flat070 = (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) := by decide +kernel
theorem block011_data_flat070_original : block011_data_flat070 = (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) := by
  rw [block011_data_flat070_step]
def block011_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1411, Int.ofNat (nat_lit 5453792467200))]
theorem block011_data_flat071_step : block011_data_flat071 = (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) := by decide +kernel
theorem block011_data_flat071_original : block011_data_flat071 = (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) := by
  rw [block011_data_flat071_step]
def block011_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat072_step : block011_data_flat072 = (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded) := by decide +kernel
theorem block011_data_flat072_original : block011_data_flat072 = (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded) := by
  rw [block011_data_flat072_step]
def block011_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat073_step : block011_data_flat073 = (CoefficientMerge.fastMerge block011_data_flat071 block011_data_flat072) := by decide +kernel
theorem block011_data_flat073_original : block011_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded)) := by
  rw [block011_data_flat073_step, block011_data_flat071_original, block011_data_flat072_original]
def block011_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat074_step : block011_data_flat074 = (CoefficientMerge.fastMerge block011_data_flat070 block011_data_flat073) := by decide +kernel
theorem block011_data_flat074_original : block011_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))) := by
  rw [block011_data_flat074_step, block011_data_flat070_original, block011_data_flat073_original]
def block011_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat075_step : block011_data_flat075 = (CoefficientMerge.fastMerge block011_data_flat069 block011_data_flat074) := by decide +kernel
theorem block011_data_flat075_original : block011_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded)))) := by
  rw [block011_data_flat075_step, block011_data_flat069_original, block011_data_flat074_original]
def block011_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat076_step : block011_data_flat076 = (CoefficientMerge.fastMerge block011_data_flat066 block011_data_flat075) := by decide +kernel
theorem block011_data_flat076_original : block011_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))))) := by
  rw [block011_data_flat076_step, block011_data_flat066_original, block011_data_flat075_original]
def block011_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800)), (nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat077_step : block011_data_flat077 = (CoefficientMerge.fastMerge block011_data_flat057 block011_data_flat076) := by decide +kernel
theorem block011_data_flat077_original : block011_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded)))))) := by
  rw [block011_data_flat077_step, block011_data_flat057_original, block011_data_flat076_original]
def block011_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560)), (nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600)), (nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800)), (nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400))]
theorem block011_data_flat078_step : block011_data_flat078 = (CoefficientMerge.fastMerge block011_data_flat038 block011_data_flat077) := by decide +kernel
theorem block011_data_flat078_original : block011_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))))))) := by
  rw [block011_data_flat078_step, block011_data_flat038_original, block011_data_flat077_original]
def block011_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200))]
theorem block011_data_flat079_step : block011_data_flat079 = (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) := by decide +kernel
theorem block011_data_flat079_original : block011_data_flat079 = (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) := by
  rw [block011_data_flat079_step]
def block011_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 11227298865408))]
theorem block011_data_flat080_step : block011_data_flat080 = (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded) := by decide +kernel
theorem block011_data_flat080_original : block011_data_flat080 = (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded) := by
  rw [block011_data_flat080_step]
def block011_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408))]
theorem block011_data_flat081_step : block011_data_flat081 = (CoefficientMerge.fastMerge block011_data_flat079 block011_data_flat080) := by decide +kernel
theorem block011_data_flat081_original : block011_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) := by
  rw [block011_data_flat081_step, block011_data_flat079_original, block011_data_flat080_original]
def block011_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 11504863641600))]
theorem block011_data_flat082_step : block011_data_flat082 = (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) := by decide +kernel
theorem block011_data_flat082_original : block011_data_flat082 = (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) := by
  rw [block011_data_flat082_step]
def block011_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 11632437734400))]
theorem block011_data_flat083_step : block011_data_flat083 = (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) := by decide +kernel
theorem block011_data_flat083_original : block011_data_flat083 = (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) := by
  rw [block011_data_flat083_step]
def block011_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1417, Int.ofNat (nat_lit 11760011827200))]
theorem block011_data_flat084_step : block011_data_flat084 = (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded) := by decide +kernel
theorem block011_data_flat084_original : block011_data_flat084 = (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded) := by
  rw [block011_data_flat084_step]
def block011_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200))]
theorem block011_data_flat085_step : block011_data_flat085 = (CoefficientMerge.fastMerge block011_data_flat083 block011_data_flat084) := by decide +kernel
theorem block011_data_flat085_original : block011_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)) := by
  rw [block011_data_flat085_step, block011_data_flat083_original, block011_data_flat084_original]
def block011_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200))]
theorem block011_data_flat086_step : block011_data_flat086 = (CoefficientMerge.fastMerge block011_data_flat082 block011_data_flat085) := by decide +kernel
theorem block011_data_flat086_original : block011_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded))) := by
  rw [block011_data_flat086_step, block011_data_flat082_original, block011_data_flat085_original]
def block011_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200))]
theorem block011_data_flat087_step : block011_data_flat087 = (CoefficientMerge.fastMerge block011_data_flat081 block011_data_flat086) := by decide +kernel
theorem block011_data_flat087_original : block011_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) := by
  rw [block011_data_flat087_step, block011_data_flat081_original, block011_data_flat086_original]
def block011_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 11263738752000))]
theorem block011_data_flat088_step : block011_data_flat088 = (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) := by decide +kernel
theorem block011_data_flat088_original : block011_data_flat088 = (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) := by
  rw [block011_data_flat088_step]
def block011_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1419, Int.ofNat (nat_lit 7479371244800))]
theorem block011_data_flat089_step : block011_data_flat089 = (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded) := by decide +kernel
theorem block011_data_flat089_original : block011_data_flat089 = (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded) := by
  rw [block011_data_flat089_step]
def block011_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800))]
theorem block011_data_flat090_step : block011_data_flat090 = (CoefficientMerge.fastMerge block011_data_flat088 block011_data_flat089) := by decide +kernel
theorem block011_data_flat090_original : block011_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) := by
  rw [block011_data_flat090_step, block011_data_flat088_original, block011_data_flat089_original]
def block011_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1420, Int.ofNat (nat_lit 7015608633600))]
theorem block011_data_flat091_step : block011_data_flat091 = (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) := by decide +kernel
theorem block011_data_flat091_original : block011_data_flat091 = (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) := by
  rw [block011_data_flat091_step]
def block011_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 7429257964800))]
theorem block011_data_flat092_step : block011_data_flat092 = (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) := by decide +kernel
theorem block011_data_flat092_original : block011_data_flat092 = (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) := by
  rw [block011_data_flat092_step]
def block011_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1422, Int.ofNat (nat_lit 15664552243200))]
theorem block011_data_flat093_step : block011_data_flat093 = (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded) := by decide +kernel
theorem block011_data_flat093_original : block011_data_flat093 = (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded) := by
  rw [block011_data_flat093_step]
def block011_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200))]
theorem block011_data_flat094_step : block011_data_flat094 = (CoefficientMerge.fastMerge block011_data_flat092 block011_data_flat093) := by decide +kernel
theorem block011_data_flat094_original : block011_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded)) := by
  rw [block011_data_flat094_step, block011_data_flat092_original, block011_data_flat093_original]
def block011_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200))]
theorem block011_data_flat095_step : block011_data_flat095 = (CoefficientMerge.fastMerge block011_data_flat091 block011_data_flat094) := by decide +kernel
theorem block011_data_flat095_original : block011_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))) := by
  rw [block011_data_flat095_step, block011_data_flat091_original, block011_data_flat094_original]
def block011_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200))]
theorem block011_data_flat096_step : block011_data_flat096 = (CoefficientMerge.fastMerge block011_data_flat090 block011_data_flat095) := by decide +kernel
theorem block011_data_flat096_original : block011_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded)))) := by
  rw [block011_data_flat096_step, block011_data_flat090_original, block011_data_flat095_original]
def block011_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200))]
theorem block011_data_flat097_step : block011_data_flat097 = (CoefficientMerge.fastMerge block011_data_flat087 block011_data_flat096) := by decide +kernel
theorem block011_data_flat097_original : block011_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) := by
  rw [block011_data_flat097_step, block011_data_flat087_original, block011_data_flat096_original]
def block011_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1423, Int.ofNat (nat_lit 6941794456800))]
theorem block011_data_flat098_step : block011_data_flat098 = (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) := by decide +kernel
theorem block011_data_flat098_original : block011_data_flat098 = (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) := by
  rw [block011_data_flat098_step]
def block011_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1424, Int.ofNat (nat_lit 12142322841600))]
theorem block011_data_flat099_step : block011_data_flat099 = (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded) := by decide +kernel
theorem block011_data_flat099_original : block011_data_flat099 = (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded) := by
  rw [block011_data_flat099_step]
def block011_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600))]
theorem block011_data_flat100_step : block011_data_flat100 = (CoefficientMerge.fastMerge block011_data_flat098 block011_data_flat099) := by decide +kernel
theorem block011_data_flat100_original : block011_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) := by
  rw [block011_data_flat100_step, block011_data_flat098_original, block011_data_flat099_original]
def block011_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1425, Int.ofNat (nat_lit 9407502064800))]
theorem block011_data_flat101_step : block011_data_flat101 = (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) := by decide +kernel
theorem block011_data_flat101_original : block011_data_flat101 = (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) := by
  rw [block011_data_flat101_step]
def block011_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1426, Int.ofNat (nat_lit 10908913831200))]
theorem block011_data_flat102_step : block011_data_flat102 = (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) := by decide +kernel
theorem block011_data_flat102_original : block011_data_flat102 = (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) := by
  rw [block011_data_flat102_step]
def block011_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1427, Int.ofNat (nat_lit 12410325597600))]
theorem block011_data_flat103_step : block011_data_flat103 = (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded) := by decide +kernel
theorem block011_data_flat103_original : block011_data_flat103 = (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded) := by
  rw [block011_data_flat103_step]
def block011_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600))]
theorem block011_data_flat104_step : block011_data_flat104 = (CoefficientMerge.fastMerge block011_data_flat102 block011_data_flat103) := by decide +kernel
theorem block011_data_flat104_original : block011_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)) := by
  rw [block011_data_flat104_step, block011_data_flat102_original, block011_data_flat103_original]
def block011_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600))]
theorem block011_data_flat105_step : block011_data_flat105 = (CoefficientMerge.fastMerge block011_data_flat101 block011_data_flat104) := by decide +kernel
theorem block011_data_flat105_original : block011_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded))) := by
  rw [block011_data_flat105_step, block011_data_flat101_original, block011_data_flat104_original]
def block011_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600))]
theorem block011_data_flat106_step : block011_data_flat106 = (CoefficientMerge.fastMerge block011_data_flat100 block011_data_flat105) := by decide +kernel
theorem block011_data_flat106_original : block011_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) := by
  rw [block011_data_flat106_step, block011_data_flat100_original, block011_data_flat105_original]
def block011_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 8572592448000))]
theorem block011_data_flat107_step : block011_data_flat107 = (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) := by decide +kernel
theorem block011_data_flat107_original : block011_data_flat107 = (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) := by
  rw [block011_data_flat107_step]
def block011_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 15532145798400))]
theorem block011_data_flat108_step : block011_data_flat108 = (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded) := by decide +kernel
theorem block011_data_flat108_original : block011_data_flat108 = (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded) := by
  rw [block011_data_flat108_step]
def block011_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400))]
theorem block011_data_flat109_step : block011_data_flat109 = (CoefficientMerge.fastMerge block011_data_flat107 block011_data_flat108) := by decide +kernel
theorem block011_data_flat109_original : block011_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) := by
  rw [block011_data_flat109_step, block011_data_flat107_original, block011_data_flat108_original]
def block011_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 12347854101504))]
theorem block011_data_flat110_step : block011_data_flat110 = (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) := by decide +kernel
theorem block011_data_flat110_original : block011_data_flat110 = (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) := by
  rw [block011_data_flat110_step]
def block011_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 12361384687104))]
theorem block011_data_flat111_step : block011_data_flat111 = (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) := by decide +kernel
theorem block011_data_flat111_original : block011_data_flat111 = (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) := by
  rw [block011_data_flat111_step]
def block011_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat112_step : block011_data_flat112 = (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded) := by decide +kernel
theorem block011_data_flat112_original : block011_data_flat112 = (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded) := by
  rw [block011_data_flat112_step]
def block011_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat113_step : block011_data_flat113 = (CoefficientMerge.fastMerge block011_data_flat111 block011_data_flat112) := by decide +kernel
theorem block011_data_flat113_original : block011_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)) := by
  rw [block011_data_flat113_step, block011_data_flat111_original, block011_data_flat112_original]
def block011_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat114_step : block011_data_flat114 = (CoefficientMerge.fastMerge block011_data_flat110 block011_data_flat113) := by decide +kernel
theorem block011_data_flat114_original : block011_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded))) := by
  rw [block011_data_flat114_step, block011_data_flat110_original, block011_data_flat113_original]
def block011_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat115_step : block011_data_flat115 = (CoefficientMerge.fastMerge block011_data_flat109 block011_data_flat114) := by decide +kernel
theorem block011_data_flat115_original : block011_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))) := by
  rw [block011_data_flat115_step, block011_data_flat109_original, block011_data_flat114_original]
def block011_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat116_step : block011_data_flat116 = (CoefficientMerge.fastMerge block011_data_flat106 block011_data_flat115) := by decide +kernel
theorem block011_data_flat116_original : block011_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded))))) := by
  rw [block011_data_flat116_step, block011_data_flat106_original, block011_data_flat115_original]
def block011_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200)), (nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304))]
theorem block011_data_flat117_step : block011_data_flat117 = (CoefficientMerge.fastMerge block011_data_flat097 block011_data_flat116) := by decide +kernel
theorem block011_data_flat117_original : block011_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))))) := by
  rw [block011_data_flat117_step, block011_data_flat097_original, block011_data_flat116_original]
def block011_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 13961859669504))]
theorem block011_data_flat118_step : block011_data_flat118 = (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) := by decide +kernel
theorem block011_data_flat118_original : block011_data_flat118 = (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) := by
  rw [block011_data_flat118_step]
def block011_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 14138249992704))]
theorem block011_data_flat119_step : block011_data_flat119 = (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded) := by decide +kernel
theorem block011_data_flat119_original : block011_data_flat119 = (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded) := by
  rw [block011_data_flat119_step]
def block011_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704))]
theorem block011_data_flat120_step : block011_data_flat120 = (CoefficientMerge.fastMerge block011_data_flat118 block011_data_flat119) := by decide +kernel
theorem block011_data_flat120_original : block011_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) := by
  rw [block011_data_flat120_step, block011_data_flat118_original, block011_data_flat119_original]
def block011_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1440, Int.ofNat (nat_lit 11604495183104))]
theorem block011_data_flat121_step : block011_data_flat121 = (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) := by decide +kernel
theorem block011_data_flat121_original : block011_data_flat121 = (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) := by
  rw [block011_data_flat121_step]
def block011_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1441, Int.ofNat (nat_lit 11137833160704))]
theorem block011_data_flat122_step : block011_data_flat122 = (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) := by decide +kernel
theorem block011_data_flat122_original : block011_data_flat122 = (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) := by
  rw [block011_data_flat122_step]
def block011_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1442, Int.ofNat (nat_lit 11810496559104))]
theorem block011_data_flat123_step : block011_data_flat123 = (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded) := by decide +kernel
theorem block011_data_flat123_original : block011_data_flat123 = (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded) := by
  rw [block011_data_flat123_step]
def block011_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104))]
theorem block011_data_flat124_step : block011_data_flat124 = (CoefficientMerge.fastMerge block011_data_flat122 block011_data_flat123) := by decide +kernel
theorem block011_data_flat124_original : block011_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)) := by
  rw [block011_data_flat124_step, block011_data_flat122_original, block011_data_flat123_original]
def block011_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104))]
theorem block011_data_flat125_step : block011_data_flat125 = (CoefficientMerge.fastMerge block011_data_flat121 block011_data_flat124) := by decide +kernel
theorem block011_data_flat125_original : block011_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded))) := by
  rw [block011_data_flat125_step, block011_data_flat121_original, block011_data_flat124_original]
def block011_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104))]
theorem block011_data_flat126_step : block011_data_flat126 = (CoefficientMerge.fastMerge block011_data_flat120 block011_data_flat125) := by decide +kernel
theorem block011_data_flat126_original : block011_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) := by
  rw [block011_data_flat126_step, block011_data_flat120_original, block011_data_flat125_original]
def block011_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1443, Int.ofNat (nat_lit 21229717077504))]
theorem block011_data_flat127_step : block011_data_flat127 = (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) := by decide +kernel
theorem block011_data_flat127_original : block011_data_flat127 = (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) := by
  rw [block011_data_flat127_step]
def block011_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1444, Int.ofNat (nat_lit 12805392234240))]
theorem block011_data_flat128_step : block011_data_flat128 = (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded) := by decide +kernel
theorem block011_data_flat128_original : block011_data_flat128 = (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded) := by
  rw [block011_data_flat128_step]
def block011_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240))]
theorem block011_data_flat129_step : block011_data_flat129 = (CoefficientMerge.fastMerge block011_data_flat127 block011_data_flat128) := by decide +kernel
theorem block011_data_flat129_original : block011_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) := by
  rw [block011_data_flat129_step, block011_data_flat127_original, block011_data_flat128_original]
def block011_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1445, Int.ofNat (nat_lit 19052814472704))]
theorem block011_data_flat130_step : block011_data_flat130 = (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) := by decide +kernel
theorem block011_data_flat130_original : block011_data_flat130 = (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) := by
  rw [block011_data_flat130_step]
def block011_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1446, Int.ofNat (nat_lit 17717790074112))]
theorem block011_data_flat131_step : block011_data_flat131 = (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) := by decide +kernel
theorem block011_data_flat131_original : block011_data_flat131 = (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) := by
  rw [block011_data_flat131_step]
def block011_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1447, Int.ofNat (nat_lit 20763990639360))]
theorem block011_data_flat132_step : block011_data_flat132 = (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded) := by decide +kernel
theorem block011_data_flat132_original : block011_data_flat132 = (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded) := by
  rw [block011_data_flat132_step]
def block011_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360))]
theorem block011_data_flat133_step : block011_data_flat133 = (CoefficientMerge.fastMerge block011_data_flat131 block011_data_flat132) := by decide +kernel
theorem block011_data_flat133_original : block011_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded)) := by
  rw [block011_data_flat133_step, block011_data_flat131_original, block011_data_flat132_original]
def block011_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360))]
theorem block011_data_flat134_step : block011_data_flat134 = (CoefficientMerge.fastMerge block011_data_flat130 block011_data_flat133) := by decide +kernel
theorem block011_data_flat134_original : block011_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))) := by
  rw [block011_data_flat134_step, block011_data_flat130_original, block011_data_flat133_original]
def block011_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360))]
theorem block011_data_flat135_step : block011_data_flat135 = (CoefficientMerge.fastMerge block011_data_flat129 block011_data_flat134) := by decide +kernel
theorem block011_data_flat135_original : block011_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded)))) := by
  rw [block011_data_flat135_step, block011_data_flat129_original, block011_data_flat134_original]
def block011_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360))]
theorem block011_data_flat136_step : block011_data_flat136 = (CoefficientMerge.fastMerge block011_data_flat126 block011_data_flat135) := by decide +kernel
theorem block011_data_flat136_original : block011_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) := by
  rw [block011_data_flat136_step, block011_data_flat126_original, block011_data_flat135_original]
def block011_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 23810191204608))]
theorem block011_data_flat137_step : block011_data_flat137 = (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) := by decide +kernel
theorem block011_data_flat137_original : block011_data_flat137 = (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) := by
  rw [block011_data_flat137_step]
def block011_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 12088611763200))]
theorem block011_data_flat138_step : block011_data_flat138 = (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded) := by decide +kernel
theorem block011_data_flat138_original : block011_data_flat138 = (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded) := by
  rw [block011_data_flat138_step]
def block011_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200))]
theorem block011_data_flat139_step : block011_data_flat139 = (CoefficientMerge.fastMerge block011_data_flat137 block011_data_flat138) := by decide +kernel
theorem block011_data_flat139_original : block011_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) := by
  rw [block011_data_flat139_step, block011_data_flat137_original, block011_data_flat138_original]
def block011_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 21174628264704))]
theorem block011_data_flat140_step : block011_data_flat140 = (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) := by decide +kernel
theorem block011_data_flat140_original : block011_data_flat140 = (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) := by
  rw [block011_data_flat140_step]
def block011_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 17391473769600))]
theorem block011_data_flat141_step : block011_data_flat141 = (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) := by decide +kernel
theorem block011_data_flat141_original : block011_data_flat141 = (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) := by
  rw [block011_data_flat141_step]
def block011_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 14851113177600))]
theorem block011_data_flat142_step : block011_data_flat142 = (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded) := by decide +kernel
theorem block011_data_flat142_original : block011_data_flat142 = (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded) := by
  rw [block011_data_flat142_step]
def block011_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600))]
theorem block011_data_flat143_step : block011_data_flat143 = (CoefficientMerge.fastMerge block011_data_flat141 block011_data_flat142) := by decide +kernel
theorem block011_data_flat143_original : block011_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)) := by
  rw [block011_data_flat143_step, block011_data_flat141_original, block011_data_flat142_original]
def block011_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600))]
theorem block011_data_flat144_step : block011_data_flat144 = (CoefficientMerge.fastMerge block011_data_flat140 block011_data_flat143) := by decide +kernel
theorem block011_data_flat144_original : block011_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded))) := by
  rw [block011_data_flat144_step, block011_data_flat140_original, block011_data_flat143_original]
def block011_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600))]
theorem block011_data_flat145_step : block011_data_flat145 = (CoefficientMerge.fastMerge block011_data_flat139 block011_data_flat144) := by decide +kernel
theorem block011_data_flat145_original : block011_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) := by
  rw [block011_data_flat145_step, block011_data_flat139_original, block011_data_flat144_original]
def block011_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 15271527801600))]
theorem block011_data_flat146_step : block011_data_flat146 = (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) := by decide +kernel
theorem block011_data_flat146_original : block011_data_flat146 = (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) := by
  rw [block011_data_flat146_step]
def block011_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1460, Int.ofNat (nat_lit 15121004774400))]
theorem block011_data_flat147_step : block011_data_flat147 = (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded) := by decide +kernel
theorem block011_data_flat147_original : block011_data_flat147 = (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded) := by
  rw [block011_data_flat147_step]
def block011_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400))]
theorem block011_data_flat148_step : block011_data_flat148 = (CoefficientMerge.fastMerge block011_data_flat146 block011_data_flat147) := by decide +kernel
theorem block011_data_flat148_original : block011_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) := by
  rw [block011_data_flat148_step, block011_data_flat146_original, block011_data_flat147_original]
def block011_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 13264025600000))]
theorem block011_data_flat149_step : block011_data_flat149 = (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) := by decide +kernel
theorem block011_data_flat149_original : block011_data_flat149 = (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) := by
  rw [block011_data_flat149_step]
def block011_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 13150125273600))]
theorem block011_data_flat150_step : block011_data_flat150 = (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) := by decide +kernel
theorem block011_data_flat150_original : block011_data_flat150 = (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) := by
  rw [block011_data_flat150_step]
def block011_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat151_step : block011_data_flat151 = (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded) := by decide +kernel
theorem block011_data_flat151_original : block011_data_flat151 = (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded) := by
  rw [block011_data_flat151_step]
def block011_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat152_step : block011_data_flat152 = (CoefficientMerge.fastMerge block011_data_flat150 block011_data_flat151) := by decide +kernel
theorem block011_data_flat152_original : block011_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded)) := by
  rw [block011_data_flat152_step, block011_data_flat150_original, block011_data_flat151_original]
def block011_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat153_step : block011_data_flat153 = (CoefficientMerge.fastMerge block011_data_flat149 block011_data_flat152) := by decide +kernel
theorem block011_data_flat153_original : block011_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded))) := by
  rw [block011_data_flat153_step, block011_data_flat149_original, block011_data_flat152_original]
def block011_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat154_step : block011_data_flat154 = (CoefficientMerge.fastMerge block011_data_flat148 block011_data_flat153) := by decide +kernel
theorem block011_data_flat154_original : block011_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded)))) := by
  rw [block011_data_flat154_step, block011_data_flat148_original, block011_data_flat153_original]
def block011_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat155_step : block011_data_flat155 = (CoefficientMerge.fastMerge block011_data_flat145 block011_data_flat154) := by decide +kernel
theorem block011_data_flat155_original : block011_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded))))) := by
  rw [block011_data_flat155_step, block011_data_flat145_original, block011_data_flat154_original]
def block011_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360)), (nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat156_step : block011_data_flat156 = (CoefficientMerge.fastMerge block011_data_flat136 block011_data_flat155) := by decide +kernel
theorem block011_data_flat156_original : block011_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded)))))) := by
  rw [block011_data_flat156_step, block011_data_flat136_original, block011_data_flat155_original]
def block011_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200)), (nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304)), (nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360)), (nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat157_step : block011_data_flat157 = (CoefficientMerge.fastMerge block011_data_flat117 block011_data_flat156) := by decide +kernel
theorem block011_data_flat157_original : block011_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded))))))) := by
  rw [block011_data_flat157_step, block011_data_flat117_original, block011_data_flat156_original]
def block011_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560)), (nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600)), (nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800)), (nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400)), (nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200)), (nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304)), (nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360)), (nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat158_step : block011_data_flat158 = (CoefficientMerge.fastMerge block011_data_flat078 block011_data_flat157) := by decide +kernel
theorem block011_data_flat158_original : block011_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded)))))))) := by
  rw [block011_data_flat158_step, block011_data_flat078_original, block011_data_flat157_original]
def block011_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1194, Int.ofNat (nat_lit 51478079385600)), (nat_lit 1195, Int.ofNat (nat_lit 39762525196800)), (nat_lit 1196, Int.ofNat (nat_lit 56627433676800)), (nat_lit 1212, Int.ofNat (nat_lit 33575181696000)), (nat_lit 1213, Int.ofNat (nat_lit 55106209267200)), (nat_lit 1214, Int.ofNat (nat_lit 75090472934400)), (nat_lit 1215, Int.ofNat (nat_lit 65114976729600)), (nat_lit 1216, Int.ofNat (nat_lit 39869803411200)), (nat_lit 1217, Int.ofNat (nat_lit 60710287881600)), (nat_lit 1234, Int.ofNat (nat_lit 22698910402560)), (nat_lit 1235, Int.ofNat (nat_lit 61504901337600)), (nat_lit 1236, Int.ofNat (nat_lit 60041007129600)), (nat_lit 1237, Int.ofNat (nat_lit 39977081625600)), (nat_lit 1238, Int.ofNat (nat_lit 47368164009600)), (nat_lit 1256, Int.ofNat (nat_lit 39973873766400)), (nat_lit 1257, Int.ofNat (nat_lit 61939813017600)), (nat_lit 1258, Int.ofNat (nat_lit 39050030880000)), (nat_lit 1259, Int.ofNat (nat_lit 49287368592000)), (nat_lit 1278, Int.ofNat (nat_lit 20684399500800)), (nat_lit 1279, Int.ofNat (nat_lit 25066859529600)), (nat_lit 1280, Int.ofNat (nat_lit 36979573680000)), (nat_lit 1300, Int.ofNat (nat_lit 1177160947200)), (nat_lit 1301, Int.ofNat (nat_lit 14227652376000)), (nat_lit 1322, Int.ofNat (nat_lit 11225070460800)), (nat_lit 1389, Int.ofNat (nat_lit 2137832524800)), (nat_lit 1390, Int.ofNat (nat_lit 5713773004800)), (nat_lit 1391, Int.ofNat (nat_lit 6505426397952)), (nat_lit 1392, Int.ofNat (nat_lit 6259026816000)), (nat_lit 1393, Int.ofNat (nat_lit 7013098571904)), (nat_lit 1394, Int.ofNat (nat_lit 6815549260800)), (nat_lit 1395, Int.ofNat (nat_lit 6543004608000)), (nat_lit 1396, Int.ofNat (nat_lit 6270459955200)), (nat_lit 1397, Int.ofNat (nat_lit 5685991718400)), (nat_lit 1398, Int.ofNat (nat_lit 3051970342400)), (nat_lit 1399, Int.ofNat (nat_lit 2161027814400)), (nat_lit 1400, Int.ofNat (nat_lit 2147497228800)), (nat_lit 1401, Int.ofNat (nat_lit 6541071667200)), (nat_lit 1403, Int.ofNat (nat_lit 4107293568000)), (nat_lit 1411, Int.ofNat (nat_lit 5453792467200)), (nat_lit 1412, Int.ofNat (nat_lit 8897326502400)), (nat_lit 1413, Int.ofNat (nat_lit 9046491955200)), (nat_lit 1414, Int.ofNat (nat_lit 11227298865408)), (nat_lit 1415, Int.ofNat (nat_lit 11504863641600)), (nat_lit 1416, Int.ofNat (nat_lit 11632437734400)), (nat_lit 1417, Int.ofNat (nat_lit 11760011827200)), (nat_lit 1418, Int.ofNat (nat_lit 11263738752000)), (nat_lit 1419, Int.ofNat (nat_lit 7479371244800)), (nat_lit 1420, Int.ofNat (nat_lit 7015608633600)), (nat_lit 1421, Int.ofNat (nat_lit 7429257964800)), (nat_lit 1422, Int.ofNat (nat_lit 15664552243200)), (nat_lit 1423, Int.ofNat (nat_lit 6941794456800)), (nat_lit 1424, Int.ofNat (nat_lit 12142322841600)), (nat_lit 1425, Int.ofNat (nat_lit 9407502064800)), (nat_lit 1426, Int.ofNat (nat_lit 10908913831200)), (nat_lit 1427, Int.ofNat (nat_lit 12410325597600)), (nat_lit 1433, Int.ofNat (nat_lit 8572592448000)), (nat_lit 1434, Int.ofNat (nat_lit 15532145798400)), (nat_lit 1435, Int.ofNat (nat_lit 12347854101504)), (nat_lit 1436, Int.ofNat (nat_lit 12361384687104)), (nat_lit 1437, Int.ofNat (nat_lit 13891307330304)), (nat_lit 1438, Int.ofNat (nat_lit 13961859669504)), (nat_lit 1439, Int.ofNat (nat_lit 14138249992704)), (nat_lit 1440, Int.ofNat (nat_lit 11604495183104)), (nat_lit 1441, Int.ofNat (nat_lit 11137833160704)), (nat_lit 1442, Int.ofNat (nat_lit 11810496559104)), (nat_lit 1443, Int.ofNat (nat_lit 21229717077504)), (nat_lit 1444, Int.ofNat (nat_lit 12805392234240)), (nat_lit 1445, Int.ofNat (nat_lit 19052814472704)), (nat_lit 1446, Int.ofNat (nat_lit 17717790074112)), (nat_lit 1447, Int.ofNat (nat_lit 20763990639360)), (nat_lit 1448, Int.ofNat (nat_lit 23810191204608)), (nat_lit 1455, Int.ofNat (nat_lit 12088611763200)), (nat_lit 1456, Int.ofNat (nat_lit 21174628264704)), (nat_lit 1457, Int.ofNat (nat_lit 17391473769600)), (nat_lit 1458, Int.ofNat (nat_lit 14851113177600)), (nat_lit 1459, Int.ofNat (nat_lit 15271527801600)), (nat_lit 1460, Int.ofNat (nat_lit 15121004774400)), (nat_lit 1461, Int.ofNat (nat_lit 13264025600000)), (nat_lit 1462, Int.ofNat (nat_lit 13150125273600)), (nat_lit 1463, Int.ofNat (nat_lit 13913636889600))]
theorem block011_data_flat159_step : block011_data_flat159 = (CoefficientMerge.trim block011_data_flat158) := by decide +kernel
theorem block011_data_flat159_original : block011_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded))))))))) := by
  rw [block011_data_flat159_step, block011_data_flat158_original]
theorem block011_data : block011 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51478079385600 : Int) atom0736Coded) (CoefficientMerge.scale (39762525196800 : Int) atom0737Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56627433676800 : Int) atom0738Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33575181696000 : Int) atom0739Coded) (CoefficientMerge.scale (55106209267200 : Int) atom0740Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75090472934400 : Int) atom0741Coded) (CoefficientMerge.scale (65114976729600 : Int) atom0742Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39869803411200 : Int) atom0743Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60710287881600 : Int) atom0744Coded) (CoefficientMerge.scale (22698910402560 : Int) atom0745Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61504901337600 : Int) atom0746Coded) (CoefficientMerge.scale (60041007129600 : Int) atom0747Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39977081625600 : Int) atom0748Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47368164009600 : Int) atom0749Coded) (CoefficientMerge.scale (39973873766400 : Int) atom0750Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61939813017600 : Int) atom0751Coded) (CoefficientMerge.scale (39050030880000 : Int) atom0752Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49287368592000 : Int) atom0753Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20684399500800 : Int) atom0754Coded) (CoefficientMerge.scale (25066859529600 : Int) atom0755Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979573680000 : Int) atom0756Coded) (CoefficientMerge.scale (1177160947200 : Int) atom0757Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14227652376000 : Int) atom0758Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11225070460800 : Int) atom0759Coded) (CoefficientMerge.scale (2137832524800 : Int) atom0760Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5713773004800 : Int) atom0761Coded) (CoefficientMerge.scale (6505426397952 : Int) atom0762Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6259026816000 : Int) atom0763Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7013098571904 : Int) atom0764Coded) (CoefficientMerge.scale (6815549260800 : Int) atom0765Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6543004608000 : Int) atom0766Coded) (CoefficientMerge.scale (6270459955200 : Int) atom0767Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5685991718400 : Int) atom0768Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3051970342400 : Int) atom0769Coded) (CoefficientMerge.scale (2161027814400 : Int) atom0770Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2147497228800 : Int) atom0771Coded) (CoefficientMerge.scale (6541071667200 : Int) atom0772Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4107293568000 : Int) atom0773Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5453792467200 : Int) atom0774Coded) (CoefficientMerge.scale (8897326502400 : Int) atom0775Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9046491955200 : Int) atom0776Coded) (CoefficientMerge.scale (11227298865408 : Int) atom0777Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11504863641600 : Int) atom0778Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11632437734400 : Int) atom0779Coded) (CoefficientMerge.scale (11760011827200 : Int) atom0780Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11263738752000 : Int) atom0781Coded) (CoefficientMerge.scale (7479371244800 : Int) atom0782Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7015608633600 : Int) atom0783Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7429257964800 : Int) atom0784Coded) (CoefficientMerge.scale (15664552243200 : Int) atom0785Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6941794456800 : Int) atom0786Coded) (CoefficientMerge.scale (12142322841600 : Int) atom0787Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9407502064800 : Int) atom0788Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10908913831200 : Int) atom0789Coded) (CoefficientMerge.scale (12410325597600 : Int) atom0790Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8572592448000 : Int) atom0791Coded) (CoefficientMerge.scale (15532145798400 : Int) atom0792Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12347854101504 : Int) atom0793Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12361384687104 : Int) atom0794Coded) (CoefficientMerge.scale (13891307330304 : Int) atom0795Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13961859669504 : Int) atom0796Coded) (CoefficientMerge.scale (14138249992704 : Int) atom0797Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11604495183104 : Int) atom0798Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11137833160704 : Int) atom0799Coded) (CoefficientMerge.scale (11810496559104 : Int) atom0800Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21229717077504 : Int) atom0801Coded) (CoefficientMerge.scale (12805392234240 : Int) atom0802Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19052814472704 : Int) atom0803Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17717790074112 : Int) atom0804Coded) (CoefficientMerge.scale (20763990639360 : Int) atom0805Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23810191204608 : Int) atom0806Coded) (CoefficientMerge.scale (12088611763200 : Int) atom0807Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21174628264704 : Int) atom0808Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391473769600 : Int) atom0809Coded) (CoefficientMerge.scale (14851113177600 : Int) atom0810Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15271527801600 : Int) atom0811Coded) (CoefficientMerge.scale (15121004774400 : Int) atom0812Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13264025600000 : Int) atom0813Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13150125273600 : Int) atom0814Coded) (CoefficientMerge.scale (13913636889600 : Int) atom0815Coded)))))))) := by
  have h : block011 = block011_data_flat159 := by decide +kernel
  exact h.trans block011_data_flat159_original
theorem block011_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block011 := by
  rw [block011_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0736Coded_nonneg g hg hA hB) (atom0737Coded_nonneg g hg hA hB)) (add_nonneg (atom0738Coded_nonneg g hg hA hB) (add_nonneg (atom0739Coded_nonneg g hg hA hB) (atom0740Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0741Coded_nonneg g hg hA hB) (atom0742Coded_nonneg g hg hA hB)) (add_nonneg (atom0743Coded_nonneg g hg hA hB) (add_nonneg (atom0744Coded_nonneg g hg hA hB) (atom0745Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0746Coded_nonneg g hg hA hB) (atom0747Coded_nonneg g hg hA hB)) (add_nonneg (atom0748Coded_nonneg g hg hA hB) (add_nonneg (atom0749Coded_nonneg g hg hA hB) (atom0750Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0751Coded_nonneg g hg hA hB) (atom0752Coded_nonneg g hg hA hB)) (add_nonneg (atom0753Coded_nonneg g hg hA hB) (add_nonneg (atom0754Coded_nonneg g hg hA hB) (atom0755Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0756Coded_nonneg g hg hA hB) (atom0757Coded_nonneg g hg hA hB)) (add_nonneg (atom0758Coded_nonneg g hg hA hB) (add_nonneg (atom0759Coded_nonneg g hg hA hB) (atom0760Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0761Coded_nonneg g hg hA hB) (atom0762Coded_nonneg g hg hA hB)) (add_nonneg (atom0763Coded_nonneg g hg hA hB) (add_nonneg (atom0764Coded_nonneg g hg hA hB) (atom0765Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0766Coded_nonneg g hg hA hB) (atom0767Coded_nonneg g hg hA hB)) (add_nonneg (atom0768Coded_nonneg g hg hA hB) (add_nonneg (atom0769Coded_nonneg g hg hA hB) (atom0770Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0771Coded_nonneg g hg hA hB) (atom0772Coded_nonneg g hg hA hB)) (add_nonneg (atom0773Coded_nonneg g hg hA hB) (add_nonneg (atom0774Coded_nonneg g hg hA hB) (atom0775Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0776Coded_nonneg g hg hA hB) (atom0777Coded_nonneg g hg hA hB)) (add_nonneg (atom0778Coded_nonneg g hg hA hB) (add_nonneg (atom0779Coded_nonneg g hg hA hB) (atom0780Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0781Coded_nonneg g hg hA hB) (atom0782Coded_nonneg g hg hA hB)) (add_nonneg (atom0783Coded_nonneg g hg hA hB) (add_nonneg (atom0784Coded_nonneg g hg hA hB) (atom0785Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0786Coded_nonneg g hg hA hB) (atom0787Coded_nonneg g hg hA hB)) (add_nonneg (atom0788Coded_nonneg g hg hA hB) (add_nonneg (atom0789Coded_nonneg g hg hA hB) (atom0790Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0791Coded_nonneg g hg hA hB) (atom0792Coded_nonneg g hg hA hB)) (add_nonneg (atom0793Coded_nonneg g hg hA hB) (add_nonneg (atom0794Coded_nonneg g hg hA hB) (atom0795Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0796Coded_nonneg g hg hA hB) (atom0797Coded_nonneg g hg hA hB)) (add_nonneg (atom0798Coded_nonneg g hg hA hB) (add_nonneg (atom0799Coded_nonneg g hg hA hB) (atom0800Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0801Coded_nonneg g hg hA hB) (atom0802Coded_nonneg g hg hA hB)) (add_nonneg (atom0803Coded_nonneg g hg hA hB) (add_nonneg (atom0804Coded_nonneg g hg hA hB) (atom0805Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0806Coded_nonneg g hg hA hB) (atom0807Coded_nonneg g hg hA hB)) (add_nonneg (atom0808Coded_nonneg g hg hA hB) (add_nonneg (atom0809Coded_nonneg g hg hA hB) (atom0810Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0811Coded_nonneg g hg hA hB) (atom0812Coded_nonneg g hg hA hB)) (add_nonneg (atom0813Coded_nonneg g hg hA hB) (add_nonneg (atom0814Coded_nonneg g hg hA hB) (atom0815Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
