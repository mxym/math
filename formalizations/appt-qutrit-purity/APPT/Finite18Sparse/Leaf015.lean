-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom1135 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1135 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1135 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1135_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4737761280 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135Coded : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 1))]
theorem atom1135Coded_decode : atom1135 = SparsePolynomial.decodeCubic 18 atom1135Coded := by decide +kernel
theorem atom1135Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) := by
  have h := atom1135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1136 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1136 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1136 = ((g 16) * (g 16) * (g 16)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1136_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3915233280 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 16) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1136Coded : CoefficientMerge.Poly := [(nat_lit 5488, Int.ofNat (nat_lit 1))]
theorem atom1136Coded_decode : atom1136 = SparsePolynomial.decodeCubic 18 atom1136Coded := by decide +kernel
theorem atom1136Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded) := by
  have h := atom1136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1137 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1137 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1137 = ((g 16) * (g 16) * (g 17)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1137_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9716797440 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137Coded : CoefficientMerge.Poly := [(nat_lit 5489, Int.ofNat (nat_lit 1))]
theorem atom1137Coded_decode : atom1137 = SparsePolynomial.decodeCubic 18 atom1137Coded := by decide +kernel
theorem atom1137Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) := by
  have h := atom1137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1138 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1138 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1138 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1138_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5922201600 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138Coded : CoefficientMerge.Poly := [(nat_lit 5507, Int.ofNat (nat_lit 1))]
theorem atom1138Coded_decode : atom1138 = SparsePolynomial.decodeCubic 18 atom1138Coded := by decide +kernel
theorem atom1138Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded) := by
  have h := atom1138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block015 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 4737761280)), (nat_lit 5488, Int.ofNat (nat_lit 3915233280)), (nat_lit 5489, Int.ofNat (nat_lit 9716797440)), (nat_lit 5507, Int.ofNat (nat_lit 5922201600))]
def block015_data_flat000 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 4737761280))]
theorem block015_data_flat000_step : block015_data_flat000 = (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) := by decide +kernel
theorem block015_data_flat000_original : block015_data_flat000 = (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) := by
  rw [block015_data_flat000_step]
def block015_data_flat001 : CoefficientMerge.Poly := [(nat_lit 5488, Int.ofNat (nat_lit 3915233280))]
theorem block015_data_flat001_step : block015_data_flat001 = (CoefficientMerge.scale (3915233280 : Int) atom1136Coded) := by decide +kernel
theorem block015_data_flat001_original : block015_data_flat001 = (CoefficientMerge.scale (3915233280 : Int) atom1136Coded) := by
  rw [block015_data_flat001_step]
def block015_data_flat002 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 4737761280)), (nat_lit 5488, Int.ofNat (nat_lit 3915233280))]
theorem block015_data_flat002_step : block015_data_flat002 = (CoefficientMerge.fastMerge block015_data_flat000 block015_data_flat001) := by decide +kernel
theorem block015_data_flat002_original : block015_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded)) := by
  rw [block015_data_flat002_step, block015_data_flat000_original, block015_data_flat001_original]
def block015_data_flat003 : CoefficientMerge.Poly := [(nat_lit 5489, Int.ofNat (nat_lit 9716797440))]
theorem block015_data_flat003_step : block015_data_flat003 = (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) := by decide +kernel
theorem block015_data_flat003_original : block015_data_flat003 = (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) := by
  rw [block015_data_flat003_step]
def block015_data_flat004 : CoefficientMerge.Poly := [(nat_lit 5507, Int.ofNat (nat_lit 5922201600))]
theorem block015_data_flat004_step : block015_data_flat004 = (CoefficientMerge.scale (5922201600 : Int) atom1138Coded) := by decide +kernel
theorem block015_data_flat004_original : block015_data_flat004 = (CoefficientMerge.scale (5922201600 : Int) atom1138Coded) := by
  rw [block015_data_flat004_step]
def block015_data_flat005 : CoefficientMerge.Poly := [(nat_lit 5489, Int.ofNat (nat_lit 9716797440)), (nat_lit 5507, Int.ofNat (nat_lit 5922201600))]
theorem block015_data_flat005_step : block015_data_flat005 = (CoefficientMerge.fastMerge block015_data_flat003 block015_data_flat004) := by decide +kernel
theorem block015_data_flat005_original : block015_data_flat005 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded)) := by
  rw [block015_data_flat005_step, block015_data_flat003_original, block015_data_flat004_original]
def block015_data_flat006 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 4737761280)), (nat_lit 5488, Int.ofNat (nat_lit 3915233280)), (nat_lit 5489, Int.ofNat (nat_lit 9716797440)), (nat_lit 5507, Int.ofNat (nat_lit 5922201600))]
theorem block015_data_flat006_step : block015_data_flat006 = (CoefficientMerge.fastMerge block015_data_flat002 block015_data_flat005) := by decide +kernel
theorem block015_data_flat006_original : block015_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded))) := by
  rw [block015_data_flat006_step, block015_data_flat002_original, block015_data_flat005_original]
def block015_data_flat007 : CoefficientMerge.Poly := [(nat_lit 5183, Int.ofNat (nat_lit 4737761280)), (nat_lit 5488, Int.ofNat (nat_lit 3915233280)), (nat_lit 5489, Int.ofNat (nat_lit 9716797440)), (nat_lit 5507, Int.ofNat (nat_lit 5922201600))]
theorem block015_data_flat007_step : block015_data_flat007 = (CoefficientMerge.trim block015_data_flat006) := by decide +kernel
theorem block015_data_flat007_original : block015_data_flat007 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded)))) := by
  rw [block015_data_flat007_step, block015_data_flat006_original]
theorem block015_data : block015 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4737761280 : Int) atom1135Coded) (CoefficientMerge.scale (3915233280 : Int) atom1136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9716797440 : Int) atom1137Coded) (CoefficientMerge.scale (5922201600 : Int) atom1138Coded))) := by
  have h : block015 = block015_data_flat007 := by decide +kernel
  exact h.trans block015_data_flat007_original
theorem block015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block015 := by
  rw [block015_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (atom1135Coded_nonneg g hg hA hB) (atom1136Coded_nonneg g hg hA hB)) (add_nonneg (atom1137Coded_nonneg g hg hA hB) (atom1138Coded_nonneg g hg hA hB)))

end APPT.Finite18
