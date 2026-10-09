import APPT.Finite24Sparse.Base08
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0209 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 10, nat_lit 12, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 10, nat_lit 12, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 10, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 10, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 10, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0209_data : atom0209 = SparsePolynomial.monoTimes [10,12] 1 base08 := by decide +kernel
theorem eval_atom0209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = (quadB (outer g) ![2,2,1] * g 10 * g 12) := by
  rw [atom0209_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (559159273728 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209Coded : CoefficientMerge.Poly := [(nat_lit 252, Int.negSucc (nat_lit 7)), (nat_lit 828, Int.negSucc (nat_lit 11)), (nat_lit 1404, Int.negSucc (nat_lit 15)), (nat_lit 1980, Int.negSucc (nat_lit 15)), (nat_lit 2556, Int.negSucc (nat_lit 15)), (nat_lit 3132, Int.negSucc (nat_lit 15)), (nat_lit 3708, Int.negSucc (nat_lit 15)), (nat_lit 4284, Int.negSucc (nat_lit 15)), (nat_lit 4860, Int.negSucc (nat_lit 15)), (nat_lit 5436, Int.negSucc (nat_lit 15)), (nat_lit 6012, Int.negSucc (nat_lit 15)), (nat_lit 6036, Int.negSucc (nat_lit 15)), (nat_lit 6060, Int.negSucc (nat_lit 15)), (nat_lit 6061, Int.negSucc (nat_lit 15)), (nat_lit 6062, Int.negSucc (nat_lit 15)), (nat_lit 6063, Int.negSucc (nat_lit 15)), (nat_lit 6064, Int.negSucc (nat_lit 15)), (nat_lit 6065, Int.negSucc (nat_lit 15)), (nat_lit 6066, Int.negSucc (nat_lit 13)), (nat_lit 6067, Int.negSucc (nat_lit 9)), (nat_lit 6068, Int.negSucc (nat_lit 1)), (nat_lit 6069, Int.ofNat (nat_lit 2)), (nat_lit 6070, Int.ofNat (nat_lit 10)), (nat_lit 6071, Int.ofNat (nat_lit 18))]
theorem atom0209Coded_decode : atom0209 = SparsePolynomial.decodeCubic 24 atom0209Coded := by decide +kernel
theorem atom0209Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (559159273728 : Int) atom0209Coded) := by
  have h := atom0209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0210 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 11, nat_lit 11, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 11, nat_lit 11, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 11, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 11, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0210_data : atom0210 = SparsePolynomial.monoTimes [11,11] 1 base08 := by decide +kernel
theorem eval_atom0210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0210_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2572011413136 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210Coded : CoefficientMerge.Poly := [(nat_lit 275, Int.negSucc (nat_lit 7)), (nat_lit 851, Int.negSucc (nat_lit 11)), (nat_lit 1427, Int.negSucc (nat_lit 15)), (nat_lit 2003, Int.negSucc (nat_lit 15)), (nat_lit 2579, Int.negSucc (nat_lit 15)), (nat_lit 3155, Int.negSucc (nat_lit 15)), (nat_lit 3731, Int.negSucc (nat_lit 15)), (nat_lit 4307, Int.negSucc (nat_lit 15)), (nat_lit 4883, Int.negSucc (nat_lit 15)), (nat_lit 5459, Int.negSucc (nat_lit 15)), (nat_lit 6035, Int.negSucc (nat_lit 15)), (nat_lit 6611, Int.negSucc (nat_lit 15)), (nat_lit 6612, Int.negSucc (nat_lit 15)), (nat_lit 6613, Int.negSucc (nat_lit 15)), (nat_lit 6614, Int.negSucc (nat_lit 15)), (nat_lit 6615, Int.negSucc (nat_lit 15)), (nat_lit 6616, Int.negSucc (nat_lit 15)), (nat_lit 6617, Int.negSucc (nat_lit 15)), (nat_lit 6618, Int.negSucc (nat_lit 13)), (nat_lit 6619, Int.negSucc (nat_lit 9)), (nat_lit 6620, Int.negSucc (nat_lit 1)), (nat_lit 6621, Int.ofNat (nat_lit 2)), (nat_lit 6622, Int.ofNat (nat_lit 10)), (nat_lit 6623, Int.ofNat (nat_lit 18))]
theorem atom0210Coded_decode : atom0210 = SparsePolynomial.decodeCubic 24 atom0210Coded := by decide +kernel
theorem atom0210Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2572011413136 : Int) atom0210Coded) := by
  have h := atom0210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0211 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 11, nat_lit 12, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 11, nat_lit 12, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 11, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 11, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0211_data : atom0211 = SparsePolynomial.monoTimes [11,12] 1 base08 := by decide +kernel
theorem eval_atom0211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0211_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7092350065152 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211Coded : CoefficientMerge.Poly := [(nat_lit 276, Int.negSucc (nat_lit 7)), (nat_lit 852, Int.negSucc (nat_lit 11)), (nat_lit 1428, Int.negSucc (nat_lit 15)), (nat_lit 2004, Int.negSucc (nat_lit 15)), (nat_lit 2580, Int.negSucc (nat_lit 15)), (nat_lit 3156, Int.negSucc (nat_lit 15)), (nat_lit 3732, Int.negSucc (nat_lit 15)), (nat_lit 4308, Int.negSucc (nat_lit 15)), (nat_lit 4884, Int.negSucc (nat_lit 15)), (nat_lit 5460, Int.negSucc (nat_lit 15)), (nat_lit 6036, Int.negSucc (nat_lit 15)), (nat_lit 6612, Int.negSucc (nat_lit 15)), (nat_lit 6636, Int.negSucc (nat_lit 15)), (nat_lit 6637, Int.negSucc (nat_lit 15)), (nat_lit 6638, Int.negSucc (nat_lit 15)), (nat_lit 6639, Int.negSucc (nat_lit 15)), (nat_lit 6640, Int.negSucc (nat_lit 15)), (nat_lit 6641, Int.negSucc (nat_lit 15)), (nat_lit 6642, Int.negSucc (nat_lit 13)), (nat_lit 6643, Int.negSucc (nat_lit 9)), (nat_lit 6644, Int.negSucc (nat_lit 1)), (nat_lit 6645, Int.ofNat (nat_lit 2)), (nat_lit 6646, Int.ofNat (nat_lit 10)), (nat_lit 6647, Int.ofNat (nat_lit 18))]
theorem atom0211Coded_decode : atom0211 = SparsePolynomial.decodeCubic 24 atom0211Coded := by decide +kernel
theorem atom0211Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7092350065152 : Int) atom0211Coded) := by
  have h := atom0211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0212 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 11, nat_lit 13, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 11, nat_lit 13, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 11, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 11, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0212_data : atom0212 = SparsePolynomial.monoTimes [11,13] 1 base08 := by decide +kernel
theorem eval_atom0212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = (quadB (outer g) ![2,2,1] * g 11 * g 13) := by
  rw [atom0212_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1676193146496 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212Coded : CoefficientMerge.Poly := [(nat_lit 277, Int.negSucc (nat_lit 7)), (nat_lit 853, Int.negSucc (nat_lit 11)), (nat_lit 1429, Int.negSucc (nat_lit 15)), (nat_lit 2005, Int.negSucc (nat_lit 15)), (nat_lit 2581, Int.negSucc (nat_lit 15)), (nat_lit 3157, Int.negSucc (nat_lit 15)), (nat_lit 3733, Int.negSucc (nat_lit 15)), (nat_lit 4309, Int.negSucc (nat_lit 15)), (nat_lit 4885, Int.negSucc (nat_lit 15)), (nat_lit 5461, Int.negSucc (nat_lit 15)), (nat_lit 6037, Int.negSucc (nat_lit 15)), (nat_lit 6613, Int.negSucc (nat_lit 15)), (nat_lit 6637, Int.negSucc (nat_lit 15)), (nat_lit 6661, Int.negSucc (nat_lit 15)), (nat_lit 6662, Int.negSucc (nat_lit 15)), (nat_lit 6663, Int.negSucc (nat_lit 15)), (nat_lit 6664, Int.negSucc (nat_lit 15)), (nat_lit 6665, Int.negSucc (nat_lit 15)), (nat_lit 6666, Int.negSucc (nat_lit 13)), (nat_lit 6667, Int.negSucc (nat_lit 9)), (nat_lit 6668, Int.negSucc (nat_lit 1)), (nat_lit 6669, Int.ofNat (nat_lit 2)), (nat_lit 6670, Int.ofNat (nat_lit 10)), (nat_lit 6671, Int.ofNat (nat_lit 18))]
theorem atom0212Coded_decode : atom0212 = SparsePolynomial.decodeCubic 24 atom0212Coded := by decide +kernel
theorem atom0212Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1676193146496 : Int) atom0212Coded) := by
  have h := atom0212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0213 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 12], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 12, nat_lit 12, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 12, nat_lit 12, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 12, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 12, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 12, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0213_data : atom0213 = SparsePolynomial.monoTimes [12,12] 1 base08 := by decide +kernel
theorem eval_atom0213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = (quadB (outer g) ![2,2,1] * g 12 * g 12) := by
  rw [atom0213_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6218852276736 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213Coded : CoefficientMerge.Poly := [(nat_lit 300, Int.negSucc (nat_lit 7)), (nat_lit 876, Int.negSucc (nat_lit 11)), (nat_lit 1452, Int.negSucc (nat_lit 15)), (nat_lit 2028, Int.negSucc (nat_lit 15)), (nat_lit 2604, Int.negSucc (nat_lit 15)), (nat_lit 3180, Int.negSucc (nat_lit 15)), (nat_lit 3756, Int.negSucc (nat_lit 15)), (nat_lit 4332, Int.negSucc (nat_lit 15)), (nat_lit 4908, Int.negSucc (nat_lit 15)), (nat_lit 5484, Int.negSucc (nat_lit 15)), (nat_lit 6060, Int.negSucc (nat_lit 15)), (nat_lit 6636, Int.negSucc (nat_lit 15)), (nat_lit 7212, Int.negSucc (nat_lit 15)), (nat_lit 7213, Int.negSucc (nat_lit 15)), (nat_lit 7214, Int.negSucc (nat_lit 15)), (nat_lit 7215, Int.negSucc (nat_lit 15)), (nat_lit 7216, Int.negSucc (nat_lit 15)), (nat_lit 7217, Int.negSucc (nat_lit 15)), (nat_lit 7218, Int.negSucc (nat_lit 13)), (nat_lit 7219, Int.negSucc (nat_lit 9)), (nat_lit 7220, Int.negSucc (nat_lit 1)), (nat_lit 7221, Int.ofNat (nat_lit 2)), (nat_lit 7222, Int.ofNat (nat_lit 10)), (nat_lit 7223, Int.ofNat (nat_lit 18))]
theorem atom0213Coded_decode : atom0213 = SparsePolynomial.decodeCubic 24 atom0213Coded := by decide +kernel
theorem atom0213Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6218852276736 : Int) atom0213Coded) := by
  have h := atom0213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0214 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 12, nat_lit 13, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 12, nat_lit 13, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 12, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 12, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 12, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0214_data : atom0214 = SparsePolynomial.monoTimes [12,13] 1 base08 := by decide +kernel
theorem eval_atom0214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = (quadB (outer g) ![2,2,1] * g 12 * g 13) := by
  rw [atom0214_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6417696928896 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214Coded : CoefficientMerge.Poly := [(nat_lit 301, Int.negSucc (nat_lit 7)), (nat_lit 877, Int.negSucc (nat_lit 11)), (nat_lit 1453, Int.negSucc (nat_lit 15)), (nat_lit 2029, Int.negSucc (nat_lit 15)), (nat_lit 2605, Int.negSucc (nat_lit 15)), (nat_lit 3181, Int.negSucc (nat_lit 15)), (nat_lit 3757, Int.negSucc (nat_lit 15)), (nat_lit 4333, Int.negSucc (nat_lit 15)), (nat_lit 4909, Int.negSucc (nat_lit 15)), (nat_lit 5485, Int.negSucc (nat_lit 15)), (nat_lit 6061, Int.negSucc (nat_lit 15)), (nat_lit 6637, Int.negSucc (nat_lit 15)), (nat_lit 7213, Int.negSucc (nat_lit 15)), (nat_lit 7237, Int.negSucc (nat_lit 15)), (nat_lit 7238, Int.negSucc (nat_lit 15)), (nat_lit 7239, Int.negSucc (nat_lit 15)), (nat_lit 7240, Int.negSucc (nat_lit 15)), (nat_lit 7241, Int.negSucc (nat_lit 15)), (nat_lit 7242, Int.negSucc (nat_lit 13)), (nat_lit 7243, Int.negSucc (nat_lit 9)), (nat_lit 7244, Int.negSucc (nat_lit 1)), (nat_lit 7245, Int.ofNat (nat_lit 2)), (nat_lit 7246, Int.ofNat (nat_lit 10)), (nat_lit 7247, Int.ofNat (nat_lit 18))]
theorem atom0214Coded_decode : atom0214 = SparsePolynomial.decodeCubic 24 atom0214Coded := by decide +kernel
theorem atom0214Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6417696928896 : Int) atom0214Coded) := by
  have h := atom0214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0215 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 12, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 12, nat_lit 14, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 12, nat_lit 14, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 12, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 12, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 12, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0215_data : atom0215 = SparsePolynomial.monoTimes [12,14] 1 base08 := by decide +kernel
theorem eval_atom0215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = (quadB (outer g) ![2,2,1] * g 12 * g 14) := by
  rw [atom0215_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (562580233776 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215Coded : CoefficientMerge.Poly := [(nat_lit 302, Int.negSucc (nat_lit 7)), (nat_lit 878, Int.negSucc (nat_lit 11)), (nat_lit 1454, Int.negSucc (nat_lit 15)), (nat_lit 2030, Int.negSucc (nat_lit 15)), (nat_lit 2606, Int.negSucc (nat_lit 15)), (nat_lit 3182, Int.negSucc (nat_lit 15)), (nat_lit 3758, Int.negSucc (nat_lit 15)), (nat_lit 4334, Int.negSucc (nat_lit 15)), (nat_lit 4910, Int.negSucc (nat_lit 15)), (nat_lit 5486, Int.negSucc (nat_lit 15)), (nat_lit 6062, Int.negSucc (nat_lit 15)), (nat_lit 6638, Int.negSucc (nat_lit 15)), (nat_lit 7214, Int.negSucc (nat_lit 15)), (nat_lit 7238, Int.negSucc (nat_lit 15)), (nat_lit 7262, Int.negSucc (nat_lit 15)), (nat_lit 7263, Int.negSucc (nat_lit 15)), (nat_lit 7264, Int.negSucc (nat_lit 15)), (nat_lit 7265, Int.negSucc (nat_lit 15)), (nat_lit 7266, Int.negSucc (nat_lit 13)), (nat_lit 7267, Int.negSucc (nat_lit 9)), (nat_lit 7268, Int.negSucc (nat_lit 1)), (nat_lit 7269, Int.ofNat (nat_lit 2)), (nat_lit 7270, Int.ofNat (nat_lit 10)), (nat_lit 7271, Int.ofNat (nat_lit 18))]
theorem atom0215Coded_decode : atom0215 = SparsePolynomial.decodeCubic 24 atom0215Coded := by decide +kernel
theorem atom0215Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (562580233776 : Int) atom0215Coded) := by
  have h := atom0215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0216 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 13], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 13, nat_lit 13, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 13, nat_lit 13, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 13, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 13, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 13, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0216_data : atom0216 = SparsePolynomial.monoTimes [13,13] 1 base08 := by decide +kernel
theorem eval_atom0216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0216_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7083593193600 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216Coded : CoefficientMerge.Poly := [(nat_lit 325, Int.negSucc (nat_lit 7)), (nat_lit 901, Int.negSucc (nat_lit 11)), (nat_lit 1477, Int.negSucc (nat_lit 15)), (nat_lit 2053, Int.negSucc (nat_lit 15)), (nat_lit 2629, Int.negSucc (nat_lit 15)), (nat_lit 3205, Int.negSucc (nat_lit 15)), (nat_lit 3781, Int.negSucc (nat_lit 15)), (nat_lit 4357, Int.negSucc (nat_lit 15)), (nat_lit 4933, Int.negSucc (nat_lit 15)), (nat_lit 5509, Int.negSucc (nat_lit 15)), (nat_lit 6085, Int.negSucc (nat_lit 15)), (nat_lit 6661, Int.negSucc (nat_lit 15)), (nat_lit 7237, Int.negSucc (nat_lit 15)), (nat_lit 7813, Int.negSucc (nat_lit 15)), (nat_lit 7814, Int.negSucc (nat_lit 15)), (nat_lit 7815, Int.negSucc (nat_lit 15)), (nat_lit 7816, Int.negSucc (nat_lit 15)), (nat_lit 7817, Int.negSucc (nat_lit 15)), (nat_lit 7818, Int.negSucc (nat_lit 13)), (nat_lit 7819, Int.negSucc (nat_lit 9)), (nat_lit 7820, Int.negSucc (nat_lit 1)), (nat_lit 7821, Int.ofNat (nat_lit 2)), (nat_lit 7822, Int.ofNat (nat_lit 10)), (nat_lit 7823, Int.ofNat (nat_lit 18))]
theorem atom0216Coded_decode : atom0216 = SparsePolynomial.decodeCubic 24 atom0216Coded := by decide +kernel
theorem atom0216Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7083593193600 : Int) atom0216Coded) := by
  have h := atom0216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0217 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 13, nat_lit 14, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 13, nat_lit 14, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 13, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 13, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 13, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0217_data : atom0217 = SparsePolynomial.monoTimes [13,14] 1 base08 := by decide +kernel
theorem eval_atom0217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = (quadB (outer g) ![2,2,1] * g 13 * g 14) := by
  rw [atom0217_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7708218986160 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217Coded : CoefficientMerge.Poly := [(nat_lit 326, Int.negSucc (nat_lit 7)), (nat_lit 902, Int.negSucc (nat_lit 11)), (nat_lit 1478, Int.negSucc (nat_lit 15)), (nat_lit 2054, Int.negSucc (nat_lit 15)), (nat_lit 2630, Int.negSucc (nat_lit 15)), (nat_lit 3206, Int.negSucc (nat_lit 15)), (nat_lit 3782, Int.negSucc (nat_lit 15)), (nat_lit 4358, Int.negSucc (nat_lit 15)), (nat_lit 4934, Int.negSucc (nat_lit 15)), (nat_lit 5510, Int.negSucc (nat_lit 15)), (nat_lit 6086, Int.negSucc (nat_lit 15)), (nat_lit 6662, Int.negSucc (nat_lit 15)), (nat_lit 7238, Int.negSucc (nat_lit 15)), (nat_lit 7814, Int.negSucc (nat_lit 15)), (nat_lit 7838, Int.negSucc (nat_lit 15)), (nat_lit 7839, Int.negSucc (nat_lit 15)), (nat_lit 7840, Int.negSucc (nat_lit 15)), (nat_lit 7841, Int.negSucc (nat_lit 15)), (nat_lit 7842, Int.negSucc (nat_lit 13)), (nat_lit 7843, Int.negSucc (nat_lit 9)), (nat_lit 7844, Int.negSucc (nat_lit 1)), (nat_lit 7845, Int.ofNat (nat_lit 2)), (nat_lit 7846, Int.ofNat (nat_lit 10)), (nat_lit 7847, Int.ofNat (nat_lit 18))]
theorem atom0217Coded_decode : atom0217 = SparsePolynomial.decodeCubic 24 atom0217Coded := by decide +kernel
theorem atom0217Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7708218986160 : Int) atom0217Coded) := by
  have h := atom0217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0218 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 13, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 13, nat_lit 15, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 13, nat_lit 15, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 13, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 13, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 13, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0218_data : atom0218 = SparsePolynomial.monoTimes [13,15] 1 base08 := by decide +kernel
theorem eval_atom0218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = (quadB (outer g) ![2,2,1] * g 13 * g 15) := by
  rw [atom0218_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (678085107840 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218Coded : CoefficientMerge.Poly := [(nat_lit 327, Int.negSucc (nat_lit 7)), (nat_lit 903, Int.negSucc (nat_lit 11)), (nat_lit 1479, Int.negSucc (nat_lit 15)), (nat_lit 2055, Int.negSucc (nat_lit 15)), (nat_lit 2631, Int.negSucc (nat_lit 15)), (nat_lit 3207, Int.negSucc (nat_lit 15)), (nat_lit 3783, Int.negSucc (nat_lit 15)), (nat_lit 4359, Int.negSucc (nat_lit 15)), (nat_lit 4935, Int.negSucc (nat_lit 15)), (nat_lit 5511, Int.negSucc (nat_lit 15)), (nat_lit 6087, Int.negSucc (nat_lit 15)), (nat_lit 6663, Int.negSucc (nat_lit 15)), (nat_lit 7239, Int.negSucc (nat_lit 15)), (nat_lit 7815, Int.negSucc (nat_lit 15)), (nat_lit 7839, Int.negSucc (nat_lit 15)), (nat_lit 7863, Int.negSucc (nat_lit 15)), (nat_lit 7864, Int.negSucc (nat_lit 15)), (nat_lit 7865, Int.negSucc (nat_lit 15)), (nat_lit 7866, Int.negSucc (nat_lit 13)), (nat_lit 7867, Int.negSucc (nat_lit 9)), (nat_lit 7868, Int.negSucc (nat_lit 1)), (nat_lit 7869, Int.ofNat (nat_lit 2)), (nat_lit 7870, Int.ofNat (nat_lit 10)), (nat_lit 7871, Int.ofNat (nat_lit 18))]
theorem atom0218Coded_decode : atom0218 = SparsePolynomial.decodeCubic 24 atom0218Coded := by decide +kernel
theorem atom0218Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (678085107840 : Int) atom0218Coded) := by
  have h := atom0218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0219 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 14], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 14, nat_lit 14, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 14, nat_lit 14, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 14, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 14, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 14, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0219_data : atom0219 = SparsePolynomial.monoTimes [14,14] 1 base08 := by decide +kernel
theorem eval_atom0219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = (quadB (outer g) ![2,2,1] * g 14 * g 14) := by
  rw [atom0219_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7509374334000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219Coded : CoefficientMerge.Poly := [(nat_lit 350, Int.negSucc (nat_lit 7)), (nat_lit 926, Int.negSucc (nat_lit 11)), (nat_lit 1502, Int.negSucc (nat_lit 15)), (nat_lit 2078, Int.negSucc (nat_lit 15)), (nat_lit 2654, Int.negSucc (nat_lit 15)), (nat_lit 3230, Int.negSucc (nat_lit 15)), (nat_lit 3806, Int.negSucc (nat_lit 15)), (nat_lit 4382, Int.negSucc (nat_lit 15)), (nat_lit 4958, Int.negSucc (nat_lit 15)), (nat_lit 5534, Int.negSucc (nat_lit 15)), (nat_lit 6110, Int.negSucc (nat_lit 15)), (nat_lit 6686, Int.negSucc (nat_lit 15)), (nat_lit 7262, Int.negSucc (nat_lit 15)), (nat_lit 7838, Int.negSucc (nat_lit 15)), (nat_lit 8414, Int.negSucc (nat_lit 15)), (nat_lit 8415, Int.negSucc (nat_lit 15)), (nat_lit 8416, Int.negSucc (nat_lit 15)), (nat_lit 8417, Int.negSucc (nat_lit 15)), (nat_lit 8418, Int.negSucc (nat_lit 13)), (nat_lit 8419, Int.negSucc (nat_lit 9)), (nat_lit 8420, Int.negSucc (nat_lit 1)), (nat_lit 8421, Int.ofNat (nat_lit 2)), (nat_lit 8422, Int.ofNat (nat_lit 10)), (nat_lit 8423, Int.ofNat (nat_lit 18))]
theorem atom0219Coded_decode : atom0219 = SparsePolynomial.decodeCubic 24 atom0219Coded := by decide +kernel
theorem atom0219Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7509374334000 : Int) atom0219Coded) := by
  have h := atom0219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0220 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 14, nat_lit 15, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 14, nat_lit 15, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 14, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 14, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 14, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0220_data : atom0220 = SparsePolynomial.monoTimes [14,15] 1 base08 := by decide +kernel
theorem eval_atom0220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = (quadB (outer g) ![2,2,1] * g 14 * g 15) := by
  rw [atom0220_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7384764083760 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220Coded : CoefficientMerge.Poly := [(nat_lit 351, Int.negSucc (nat_lit 7)), (nat_lit 927, Int.negSucc (nat_lit 11)), (nat_lit 1503, Int.negSucc (nat_lit 15)), (nat_lit 2079, Int.negSucc (nat_lit 15)), (nat_lit 2655, Int.negSucc (nat_lit 15)), (nat_lit 3231, Int.negSucc (nat_lit 15)), (nat_lit 3807, Int.negSucc (nat_lit 15)), (nat_lit 4383, Int.negSucc (nat_lit 15)), (nat_lit 4959, Int.negSucc (nat_lit 15)), (nat_lit 5535, Int.negSucc (nat_lit 15)), (nat_lit 6111, Int.negSucc (nat_lit 15)), (nat_lit 6687, Int.negSucc (nat_lit 15)), (nat_lit 7263, Int.negSucc (nat_lit 15)), (nat_lit 7839, Int.negSucc (nat_lit 15)), (nat_lit 8415, Int.negSucc (nat_lit 15)), (nat_lit 8439, Int.negSucc (nat_lit 15)), (nat_lit 8440, Int.negSucc (nat_lit 15)), (nat_lit 8441, Int.negSucc (nat_lit 15)), (nat_lit 8442, Int.negSucc (nat_lit 13)), (nat_lit 8443, Int.negSucc (nat_lit 9)), (nat_lit 8444, Int.negSucc (nat_lit 1)), (nat_lit 8445, Int.ofNat (nat_lit 2)), (nat_lit 8446, Int.ofNat (nat_lit 10)), (nat_lit 8447, Int.ofNat (nat_lit 18))]
theorem atom0220Coded_decode : atom0220 = SparsePolynomial.decodeCubic 24 atom0220Coded := by decide +kernel
theorem atom0220Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7384764083760 : Int) atom0220Coded) := by
  have h := atom0220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0221 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 14, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 16, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 14, nat_lit 16, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 14, nat_lit 16, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 14, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 14, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 14, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0221_data : atom0221 = SparsePolynomial.monoTimes [14,16] 1 base08 := by decide +kernel
theorem eval_atom0221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = (quadB (outer g) ![2,2,1] * g 14 * g 16) := by
  rw [atom0221_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201182894640 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221Coded : CoefficientMerge.Poly := [(nat_lit 352, Int.negSucc (nat_lit 7)), (nat_lit 928, Int.negSucc (nat_lit 11)), (nat_lit 1504, Int.negSucc (nat_lit 15)), (nat_lit 2080, Int.negSucc (nat_lit 15)), (nat_lit 2656, Int.negSucc (nat_lit 15)), (nat_lit 3232, Int.negSucc (nat_lit 15)), (nat_lit 3808, Int.negSucc (nat_lit 15)), (nat_lit 4384, Int.negSucc (nat_lit 15)), (nat_lit 4960, Int.negSucc (nat_lit 15)), (nat_lit 5536, Int.negSucc (nat_lit 15)), (nat_lit 6112, Int.negSucc (nat_lit 15)), (nat_lit 6688, Int.negSucc (nat_lit 15)), (nat_lit 7264, Int.negSucc (nat_lit 15)), (nat_lit 7840, Int.negSucc (nat_lit 15)), (nat_lit 8416, Int.negSucc (nat_lit 15)), (nat_lit 8440, Int.negSucc (nat_lit 15)), (nat_lit 8464, Int.negSucc (nat_lit 15)), (nat_lit 8465, Int.negSucc (nat_lit 15)), (nat_lit 8466, Int.negSucc (nat_lit 13)), (nat_lit 8467, Int.negSucc (nat_lit 9)), (nat_lit 8468, Int.negSucc (nat_lit 1)), (nat_lit 8469, Int.ofNat (nat_lit 2)), (nat_lit 8470, Int.ofNat (nat_lit 10)), (nat_lit 8471, Int.ofNat (nat_lit 18))]
theorem atom0221Coded_decode : atom0221 = SparsePolynomial.decodeCubic 24 atom0221Coded := by decide +kernel
theorem atom0221Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (201182894640 : Int) atom0221Coded) := by
  have h := atom0221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0222 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 15, nat_lit 15], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 15, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 15, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 15, nat_lit 15, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 15, nat_lit 15, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 15, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 15, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 15, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0222_data : atom0222 = SparsePolynomial.monoTimes [15,15] 1 base08 := by decide +kernel
theorem eval_atom0222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = (quadB (outer g) ![2,2,1] * g 15 * g 15) := by
  rw [atom0222_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6760138291200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222Coded : CoefficientMerge.Poly := [(nat_lit 375, Int.negSucc (nat_lit 7)), (nat_lit 951, Int.negSucc (nat_lit 11)), (nat_lit 1527, Int.negSucc (nat_lit 15)), (nat_lit 2103, Int.negSucc (nat_lit 15)), (nat_lit 2679, Int.negSucc (nat_lit 15)), (nat_lit 3255, Int.negSucc (nat_lit 15)), (nat_lit 3831, Int.negSucc (nat_lit 15)), (nat_lit 4407, Int.negSucc (nat_lit 15)), (nat_lit 4983, Int.negSucc (nat_lit 15)), (nat_lit 5559, Int.negSucc (nat_lit 15)), (nat_lit 6135, Int.negSucc (nat_lit 15)), (nat_lit 6711, Int.negSucc (nat_lit 15)), (nat_lit 7287, Int.negSucc (nat_lit 15)), (nat_lit 7863, Int.negSucc (nat_lit 15)), (nat_lit 8439, Int.negSucc (nat_lit 15)), (nat_lit 9015, Int.negSucc (nat_lit 15)), (nat_lit 9016, Int.negSucc (nat_lit 15)), (nat_lit 9017, Int.negSucc (nat_lit 15)), (nat_lit 9018, Int.negSucc (nat_lit 13)), (nat_lit 9019, Int.negSucc (nat_lit 9)), (nat_lit 9020, Int.negSucc (nat_lit 1)), (nat_lit 9021, Int.ofNat (nat_lit 2)), (nat_lit 9022, Int.ofNat (nat_lit 10)), (nat_lit 9023, Int.ofNat (nat_lit 18))]
theorem atom0222Coded_decode : atom0222 = SparsePolynomial.decodeCubic 24 atom0222Coded := by decide +kernel
theorem atom0222Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6760138291200 : Int) atom0222Coded) := by
  have h := atom0222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0223 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 15, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 16, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 15, nat_lit 16, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 15, nat_lit 16, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 15, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 15, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 15, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0223_data : atom0223 = SparsePolynomial.monoTimes [15,16] 1 base08 := by decide +kernel
theorem eval_atom0223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = (quadB (outer g) ![2,2,1] * g 15 * g 16) := by
  rw [atom0223_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5732844687360 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223Coded : CoefficientMerge.Poly := [(nat_lit 376, Int.negSucc (nat_lit 7)), (nat_lit 952, Int.negSucc (nat_lit 11)), (nat_lit 1528, Int.negSucc (nat_lit 15)), (nat_lit 2104, Int.negSucc (nat_lit 15)), (nat_lit 2680, Int.negSucc (nat_lit 15)), (nat_lit 3256, Int.negSucc (nat_lit 15)), (nat_lit 3832, Int.negSucc (nat_lit 15)), (nat_lit 4408, Int.negSucc (nat_lit 15)), (nat_lit 4984, Int.negSucc (nat_lit 15)), (nat_lit 5560, Int.negSucc (nat_lit 15)), (nat_lit 6136, Int.negSucc (nat_lit 15)), (nat_lit 6712, Int.negSucc (nat_lit 15)), (nat_lit 7288, Int.negSucc (nat_lit 15)), (nat_lit 7864, Int.negSucc (nat_lit 15)), (nat_lit 8440, Int.negSucc (nat_lit 15)), (nat_lit 9016, Int.negSucc (nat_lit 15)), (nat_lit 9040, Int.negSucc (nat_lit 15)), (nat_lit 9041, Int.negSucc (nat_lit 15)), (nat_lit 9042, Int.negSucc (nat_lit 13)), (nat_lit 9043, Int.negSucc (nat_lit 9)), (nat_lit 9044, Int.negSucc (nat_lit 1)), (nat_lit 9045, Int.ofNat (nat_lit 2)), (nat_lit 9046, Int.ofNat (nat_lit 10)), (nat_lit 9047, Int.ofNat (nat_lit 18))]
theorem atom0223Coded_decode : atom0223 = SparsePolynomial.decodeCubic 24 atom0223Coded := by decide +kernel
theorem atom0223Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5732844687360 : Int) atom0223Coded) := by
  have h := atom0223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0224 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 16, nat_lit 16], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 16, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 16, nat_lit 16, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 16, nat_lit 16, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 16, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 16, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 16, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0224_data : atom0224 = SparsePolynomial.monoTimes [16,16] 1 base08 := by decide +kernel
theorem eval_atom0224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = (quadB (outer g) ![2,2,1] * g 16 * g 16) := by
  rw [atom0224_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5857454937600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224Coded : CoefficientMerge.Poly := [(nat_lit 400, Int.negSucc (nat_lit 7)), (nat_lit 976, Int.negSucc (nat_lit 11)), (nat_lit 1552, Int.negSucc (nat_lit 15)), (nat_lit 2128, Int.negSucc (nat_lit 15)), (nat_lit 2704, Int.negSucc (nat_lit 15)), (nat_lit 3280, Int.negSucc (nat_lit 15)), (nat_lit 3856, Int.negSucc (nat_lit 15)), (nat_lit 4432, Int.negSucc (nat_lit 15)), (nat_lit 5008, Int.negSucc (nat_lit 15)), (nat_lit 5584, Int.negSucc (nat_lit 15)), (nat_lit 6160, Int.negSucc (nat_lit 15)), (nat_lit 6736, Int.negSucc (nat_lit 15)), (nat_lit 7312, Int.negSucc (nat_lit 15)), (nat_lit 7888, Int.negSucc (nat_lit 15)), (nat_lit 8464, Int.negSucc (nat_lit 15)), (nat_lit 9040, Int.negSucc (nat_lit 15)), (nat_lit 9616, Int.negSucc (nat_lit 15)), (nat_lit 9617, Int.negSucc (nat_lit 15)), (nat_lit 9618, Int.negSucc (nat_lit 13)), (nat_lit 9619, Int.negSucc (nat_lit 9)), (nat_lit 9620, Int.negSucc (nat_lit 1)), (nat_lit 9621, Int.ofNat (nat_lit 2)), (nat_lit 9622, Int.ofNat (nat_lit 10)), (nat_lit 9623, Int.ofNat (nat_lit 18))]
theorem atom0224Coded_decode : atom0224 = SparsePolynomial.decodeCubic 24 atom0224Coded := by decide +kernel
theorem atom0224Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5857454937600 : Int) atom0224Coded) := by
  have h := atom0224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0225 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 16, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 17, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 16, nat_lit 17, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 16, nat_lit 17, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 16, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 16, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 16, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0225_data : atom0225 = SparsePolynomial.monoTimes [16,17] 1 base08 := by decide +kernel
theorem eval_atom0225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = (quadB (outer g) ![2,2,1] * g 16 * g 17) := by
  rw [atom0225_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2325757324800 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225Coded : CoefficientMerge.Poly := [(nat_lit 401, Int.negSucc (nat_lit 7)), (nat_lit 977, Int.negSucc (nat_lit 11)), (nat_lit 1553, Int.negSucc (nat_lit 15)), (nat_lit 2129, Int.negSucc (nat_lit 15)), (nat_lit 2705, Int.negSucc (nat_lit 15)), (nat_lit 3281, Int.negSucc (nat_lit 15)), (nat_lit 3857, Int.negSucc (nat_lit 15)), (nat_lit 4433, Int.negSucc (nat_lit 15)), (nat_lit 5009, Int.negSucc (nat_lit 15)), (nat_lit 5585, Int.negSucc (nat_lit 15)), (nat_lit 6161, Int.negSucc (nat_lit 15)), (nat_lit 6737, Int.negSucc (nat_lit 15)), (nat_lit 7313, Int.negSucc (nat_lit 15)), (nat_lit 7889, Int.negSucc (nat_lit 15)), (nat_lit 8465, Int.negSucc (nat_lit 15)), (nat_lit 9041, Int.negSucc (nat_lit 15)), (nat_lit 9617, Int.negSucc (nat_lit 15)), (nat_lit 9641, Int.negSucc (nat_lit 15)), (nat_lit 9642, Int.negSucc (nat_lit 13)), (nat_lit 9643, Int.negSucc (nat_lit 9)), (nat_lit 9644, Int.negSucc (nat_lit 1)), (nat_lit 9645, Int.ofNat (nat_lit 2)), (nat_lit 9646, Int.ofNat (nat_lit 10)), (nat_lit 9647, Int.ofNat (nat_lit 18))]
theorem atom0225Coded_decode : atom0225 = SparsePolynomial.decodeCubic 24 atom0225Coded := by decide +kernel
theorem atom0225Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2325757324800 : Int) atom0225Coded) := by
  have h := atom0225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0226 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 17, nat_lit 17, nat_lit 17], Int.negSucc (nat_lit 15)), ([nat_lit 17, nat_lit 17, nat_lit 18], Int.negSucc (nat_lit 13)), ([nat_lit 17, nat_lit 17, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 17, nat_lit 17, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 17, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 17, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 17, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0226_data : atom0226 = SparsePolynomial.monoTimes [17,17] 1 base08 := by decide +kernel
theorem eval_atom0226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = (quadB (outer g) ![2,2,1] * g 17 * g 17) := by
  rw [atom0226_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3848485132800 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 17 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226Coded : CoefficientMerge.Poly := [(nat_lit 425, Int.negSucc (nat_lit 7)), (nat_lit 1001, Int.negSucc (nat_lit 11)), (nat_lit 1577, Int.negSucc (nat_lit 15)), (nat_lit 2153, Int.negSucc (nat_lit 15)), (nat_lit 2729, Int.negSucc (nat_lit 15)), (nat_lit 3305, Int.negSucc (nat_lit 15)), (nat_lit 3881, Int.negSucc (nat_lit 15)), (nat_lit 4457, Int.negSucc (nat_lit 15)), (nat_lit 5033, Int.negSucc (nat_lit 15)), (nat_lit 5609, Int.negSucc (nat_lit 15)), (nat_lit 6185, Int.negSucc (nat_lit 15)), (nat_lit 6761, Int.negSucc (nat_lit 15)), (nat_lit 7337, Int.negSucc (nat_lit 15)), (nat_lit 7913, Int.negSucc (nat_lit 15)), (nat_lit 8489, Int.negSucc (nat_lit 15)), (nat_lit 9065, Int.negSucc (nat_lit 15)), (nat_lit 9641, Int.negSucc (nat_lit 15)), (nat_lit 10217, Int.negSucc (nat_lit 15)), (nat_lit 10218, Int.negSucc (nat_lit 13)), (nat_lit 10219, Int.negSucc (nat_lit 9)), (nat_lit 10220, Int.negSucc (nat_lit 1)), (nat_lit 10221, Int.ofNat (nat_lit 2)), (nat_lit 10222, Int.ofNat (nat_lit 10)), (nat_lit 10223, Int.ofNat (nat_lit 18))]
theorem atom0226Coded_decode : atom0226 = SparsePolynomial.decodeCubic 24 atom0226Coded := by decide +kernel
theorem atom0226Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3848485132800 : Int) atom0226Coded) := by
  have h := atom0226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0227 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 4, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 5, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 6, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 7, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 8, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 9, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 10, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 11, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 12, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 13, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 14, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 15, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 16, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 17, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 15)), ([nat_lit 18, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 13)), ([nat_lit 19, nat_lit 19, nat_lit 19], Int.negSucc (nat_lit 9)), ([nat_lit 19, nat_lit 19, nat_lit 20], Int.negSucc (nat_lit 1)), ([nat_lit 19, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 2)), ([nat_lit 19, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 10)), ([nat_lit 19, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 18))]
theorem atom0227_data : atom0227 = SparsePolynomial.monoTimes [19,19] 1 base08 := by decide +kernel
theorem eval_atom0227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = (quadB (outer g) ![2,2,1] * g 19 * g 19) := by
  rw [atom0227_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (612355645440 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 19 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227Coded : CoefficientMerge.Poly := [(nat_lit 475, Int.negSucc (nat_lit 7)), (nat_lit 1051, Int.negSucc (nat_lit 11)), (nat_lit 1627, Int.negSucc (nat_lit 15)), (nat_lit 2203, Int.negSucc (nat_lit 15)), (nat_lit 2779, Int.negSucc (nat_lit 15)), (nat_lit 3355, Int.negSucc (nat_lit 15)), (nat_lit 3931, Int.negSucc (nat_lit 15)), (nat_lit 4507, Int.negSucc (nat_lit 15)), (nat_lit 5083, Int.negSucc (nat_lit 15)), (nat_lit 5659, Int.negSucc (nat_lit 15)), (nat_lit 6235, Int.negSucc (nat_lit 15)), (nat_lit 6811, Int.negSucc (nat_lit 15)), (nat_lit 7387, Int.negSucc (nat_lit 15)), (nat_lit 7963, Int.negSucc (nat_lit 15)), (nat_lit 8539, Int.negSucc (nat_lit 15)), (nat_lit 9115, Int.negSucc (nat_lit 15)), (nat_lit 9691, Int.negSucc (nat_lit 15)), (nat_lit 10267, Int.negSucc (nat_lit 15)), (nat_lit 10843, Int.negSucc (nat_lit 13)), (nat_lit 11419, Int.negSucc (nat_lit 9)), (nat_lit 11420, Int.negSucc (nat_lit 1)), (nat_lit 11421, Int.ofNat (nat_lit 2)), (nat_lit 11422, Int.ofNat (nat_lit 10)), (nat_lit 11423, Int.ofNat (nat_lit 18))]
theorem atom0227Coded_decode : atom0227 = SparsePolynomial.decodeCubic 24 atom0227Coded := by decide +kernel
theorem atom0227Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (612355645440 : Int) atom0227Coded) := by
  have h := atom0227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0228 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 0) * (g 0) * (g 11)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2323663382304 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 0) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228Coded : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 1))]
theorem atom0228Coded_decode : atom0228 = SparsePolynomial.decodeCubic 24 atom0228Coded := by decide +kernel
theorem atom0228Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2323663382304 : Int) atom0228Coded) := by
  have h := atom0228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0229 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27162605029824 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229Coded : CoefficientMerge.Poly := [(nat_lit 12, Int.ofNat (nat_lit 1))]
theorem atom0229Coded_decode : atom0229 = SparsePolynomial.decodeCubic 24 atom0229Coded := by decide +kernel
theorem atom0229Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27162605029824 : Int) atom0229Coded) := by
  have h := atom0229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0230 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 0) * (g 0) * (g 13)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15418433923200 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 0) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230Coded : CoefficientMerge.Poly := [(nat_lit 13, Int.ofNat (nat_lit 1))]
theorem atom0230Coded_decode : atom0230 = SparsePolynomial.decodeCubic 24 atom0230Coded := by decide +kernel
theorem atom0230Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15418433923200 : Int) atom0230Coded) := by
  have h := atom0230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0231 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 0) * (g 0) * (g 18)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11502930700800 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 0) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231Coded : CoefficientMerge.Poly := [(nat_lit 18, Int.ofNat (nat_lit 1))]
theorem atom0231Coded_decode : atom0231 = SparsePolynomial.decodeCubic 24 atom0231Coded := by decide +kernel
theorem atom0231Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11502930700800 : Int) atom0231Coded) := by
  have h := atom0231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0232 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 0) * (g 0) * (g 19)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8419890124800 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 0) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232Coded : CoefficientMerge.Poly := [(nat_lit 19, Int.ofNat (nat_lit 1))]
theorem atom0232Coded_decode : atom0232 = SparsePolynomial.decodeCubic 24 atom0232Coded := by decide +kernel
theorem atom0232Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8419890124800 : Int) atom0232Coded) := by
  have h := atom0232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0233 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 0) * (g 0) * (g 20)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5336849548800 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 0) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(nat_lit 20, Int.ofNat (nat_lit 1))]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 24 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5336849548800 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 0) * (g 0) * (g 21)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2253808972800 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 0) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 1))]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 24 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2253808972800 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 1], Int.ofNat (nat_lit 1))]
theorem eval_atom0235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2338858368000 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(nat_lit 25, Int.ofNat (nat_lit 1))]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 24 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2338858368000 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60480751161600 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 1))]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 24 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60480751161600 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59959823616000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(nat_lit 27, Int.ofNat (nat_lit 1))]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 24 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59959823616000 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59438896070400 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(nat_lit 28, Int.ofNat (nat_lit 1))]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 24 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59438896070400 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62359415395200 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(nat_lit 29, Int.ofNat (nat_lit 1))]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 24 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62359415395200 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0240 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58397040979200 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240Coded : CoefficientMerge.Poly := [(nat_lit 30, Int.ofNat (nat_lit 1))]
theorem atom0240Coded_decode : atom0240 = SparsePolynomial.decodeCubic 24 atom0240Coded := by decide +kernel
theorem atom0240Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58397040979200 : Int) atom0240Coded) := by
  have h := atom0240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0241 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57876113433600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241Coded : CoefficientMerge.Poly := [(nat_lit 31, Int.ofNat (nat_lit 1))]
theorem atom0241Coded_decode : atom0241 = SparsePolynomial.decodeCubic 24 atom0241Coded := by decide +kernel
theorem atom0241Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57876113433600 : Int) atom0241Coded) := by
  have h := atom0241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0242 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57355185888000 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242Coded : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 1))]
theorem atom0242Coded_decode : atom0242 = SparsePolynomial.decodeCubic 24 atom0242Coded := by decide +kernel
theorem atom0242Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57355185888000 : Int) atom0242Coded) := by
  have h := atom0242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0243 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59840148865464 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243Coded : CoefficientMerge.Poly := [(nat_lit 33, Int.ofNat (nat_lit 1))]
theorem atom0243Coded_decode : atom0243 = SparsePolynomial.decodeCubic 24 atom0243Coded := by decide +kernel
theorem atom0243Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59840148865464 : Int) atom0243Coded) := by
  have h := atom0243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0244 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68140969836984 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244Coded : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 1))]
theorem atom0244Coded_decode : atom0244 = SparsePolynomial.decodeCubic 24 atom0244Coded := by decide +kernel
theorem atom0244Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68140969836984 : Int) atom0244Coded) := by
  have h := atom0244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0245 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79108072262208 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245Coded : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 1))]
theorem atom0245Coded_decode : atom0245 = SparsePolynomial.decodeCubic 24 atom0245Coded := by decide +kernel
theorem atom0245Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79108072262208 : Int) atom0245Coded) := by
  have h := atom0245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0246 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129806548299648 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246Coded : CoefficientMerge.Poly := [(nat_lit 36, Int.ofNat (nat_lit 1))]
theorem atom0246Coded_decode : atom0246 = SparsePolynomial.decodeCubic 24 atom0246Coded := by decide +kernel
theorem atom0246Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129806548299648 : Int) atom0246Coded) := by
  have h := atom0246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0247 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107338798828800 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247Coded : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 1))]
theorem atom0247Coded_decode : atom0247 = SparsePolynomial.decodeCubic 24 atom0247Coded := by decide +kernel
theorem atom0247Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107338798828800 : Int) atom0247Coded) := by
  have h := atom0247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0248 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77522523724800 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248Coded : CoefficientMerge.Poly := [(nat_lit 38, Int.ofNat (nat_lit 1))]
theorem atom0248Coded_decode : atom0248 = SparsePolynomial.decodeCubic 24 atom0248Coded := by decide +kernel
theorem atom0248Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77522523724800 : Int) atom0248Coded) := by
  have h := atom0248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0249 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78227402803200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249Coded : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 1))]
theorem atom0249Coded_decode : atom0249 = SparsePolynomial.decodeCubic 24 atom0249Coded := by decide +kernel
theorem atom0249Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78227402803200 : Int) atom0249Coded) := by
  have h := atom0249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0250 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73021026758400 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250Coded : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 1))]
theorem atom0250Coded_decode : atom0250 = SparsePolynomial.decodeCubic 24 atom0250Coded := by decide +kernel
theorem atom0250Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73021026758400 : Int) atom0250Coded) := by
  have h := atom0250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0251 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72781019942400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251Coded : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 1))]
theorem atom0251Coded_decode : atom0251 = SparsePolynomial.decodeCubic 24 atom0251Coded := by decide +kernel
theorem atom0251Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72781019942400 : Int) atom0251Coded) := by
  have h := atom0251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0252 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102984186412800 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252Coded : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 1))]
theorem atom0252Coded_decode : atom0252 = SparsePolynomial.decodeCubic 24 atom0252Coded := by decide +kernel
theorem atom0252Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102984186412800 : Int) atom0252Coded) := by
  have h := atom0252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0253 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40961914963200 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253Coded : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 1))]
theorem atom0253Coded_decode : atom0253 = SparsePolynomial.decodeCubic 24 atom0253Coded := by decide +kernel
theorem atom0253Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40961914963200 : Int) atom0253Coded) := by
  have h := atom0253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0254 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 0) * (g 1) * (g 20)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12512892268800 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 1) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254Coded : CoefficientMerge.Poly := [(nat_lit 44, Int.ofNat (nat_lit 1))]
theorem atom0254Coded_decode : atom0254 = SparsePolynomial.decodeCubic 24 atom0254Coded := by decide +kernel
theorem atom0254Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12512892268800 : Int) atom0254Coded) := by
  have h := atom0254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0255 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0255 = ((g 0) * (g 1) * (g 21)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5205731731200 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 1) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255Coded : CoefficientMerge.Poly := [(nat_lit 45, Int.ofNat (nat_lit 1))]
theorem atom0255Coded_decode : atom0255 = SparsePolynomial.decodeCubic 24 atom0255Coded := by decide +kernel
theorem atom0255Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5205731731200 : Int) atom0255Coded) := by
  have h := atom0255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0256 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0256 = ((g 0) * (g 1) * (g 22)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4086988550400 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 1) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256Coded : CoefficientMerge.Poly := [(nat_lit 46, Int.ofNat (nat_lit 1))]
theorem atom0256Coded_decode : atom0256 = SparsePolynomial.decodeCubic 24 atom0256Coded := by decide +kernel
theorem atom0256Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4086988550400 : Int) atom0256Coded) := by
  have h := atom0256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0257 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0257 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65275410816000 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257Coded : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 1))]
theorem atom0257Coded_decode : atom0257 = SparsePolynomial.decodeCubic 24 atom0257Coded := by decide +kernel
theorem atom0257Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65275410816000 : Int) atom0257Coded) := by
  have h := atom0257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0258 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0258 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132592007116800 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258Coded : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 1))]
theorem atom0258Coded_decode : atom0258 = SparsePolynomial.decodeCubic 24 atom0258Coded := by decide +kernel
theorem atom0258Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (132592007116800 : Int) atom0258Coded) := by
  have h := atom0258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0259 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0259 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134633192601600 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259Coded : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 1))]
theorem atom0259Coded_decode : atom0259 = SparsePolynomial.decodeCubic 24 atom0259Coded := by decide +kernel
theorem atom0259Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134633192601600 : Int) atom0259Coded) := by
  have h := atom0259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0260 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0260 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136674378086400 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260Coded : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 1))]
theorem atom0260Coded_decode : atom0260 = SparsePolynomial.decodeCubic 24 atom0260Coded := by decide +kernel
theorem atom0260Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136674378086400 : Int) atom0260Coded) := by
  have h := atom0260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0261 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0261 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (138715563571200 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261Coded : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 1))]
theorem atom0261Coded_decode : atom0261 = SparsePolynomial.decodeCubic 24 atom0261Coded := by decide +kernel
theorem atom0261Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (138715563571200 : Int) atom0261Coded) := by
  have h := atom0261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0262 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0262 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140756749056000 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262Coded : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 1))]
theorem atom0262Coded_decode : atom0262 = SparsePolynomial.decodeCubic 24 atom0262Coded := by decide +kernel
theorem atom0262Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140756749056000 : Int) atom0262Coded) := by
  have h := atom0262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0263 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0263 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142797934540800 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263Coded : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 1))]
theorem atom0263Coded_decode : atom0263 = SparsePolynomial.decodeCubic 24 atom0263Coded := by decide +kernel
theorem atom0263Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142797934540800 : Int) atom0263Coded) := by
  have h := atom0263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0264 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0264 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144839120025600 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264Coded : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 1))]
theorem atom0264Coded_decode : atom0264 = SparsePolynomial.decodeCubic 24 atom0264Coded := by decide +kernel
theorem atom0264Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144839120025600 : Int) atom0264Coded) := by
  have h := atom0264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0265 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0265 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146880305510400 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265Coded : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 1))]
theorem atom0265Coded_decode : atom0265 = SparsePolynomial.decodeCubic 24 atom0265Coded := by decide +kernel
theorem atom0265Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146880305510400 : Int) atom0265Coded) := by
  have h := atom0265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0266 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0266 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153568817759808 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266Coded : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 1))]
theorem atom0266Coded_decode : atom0266 = SparsePolynomial.decodeCubic 24 atom0266Coded := by decide +kernel
theorem atom0266Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153568817759808 : Int) atom0266Coded) := by
  have h := atom0266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0267 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0267 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205287886539648 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267Coded : CoefficientMerge.Poly := [(nat_lit 60, Int.ofNat (nat_lit 1))]
theorem atom0267Coded_decode : atom0267 = SparsePolynomial.decodeCubic 24 atom0267Coded := by decide +kernel
theorem atom0267Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205287886539648 : Int) atom0267Coded) := by
  have h := atom0267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0268 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0268 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183840729811200 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268Coded : CoefficientMerge.Poly := [(nat_lit 61, Int.ofNat (nat_lit 1))]
theorem atom0268Coded_decode : atom0268 = SparsePolynomial.decodeCubic 24 atom0268Coded := by decide +kernel
theorem atom0268Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183840729811200 : Int) atom0268Coded) := by
  have h := atom0268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0269 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0269 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155045047449600 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269Coded : CoefficientMerge.Poly := [(nat_lit 62, Int.ofNat (nat_lit 1))]
theorem atom0269Coded_decode : atom0269 = SparsePolynomial.decodeCubic 24 atom0269Coded := by decide +kernel
theorem atom0269Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155045047449600 : Int) atom0269Coded) := by
  have h := atom0269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0270 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0270 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157086232934400 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270Coded : CoefficientMerge.Poly := [(nat_lit 63, Int.ofNat (nat_lit 1))]
theorem atom0270Coded_decode : atom0270 = SparsePolynomial.decodeCubic 24 atom0270Coded := by decide +kernel
theorem atom0270Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157086232934400 : Int) atom0270Coded) := by
  have h := atom0270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0271 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0271 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159127418419200 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271Coded : CoefficientMerge.Poly := [(nat_lit 64, Int.ofNat (nat_lit 1))]
theorem atom0271Coded_decode : atom0271 = SparsePolynomial.decodeCubic 24 atom0271Coded := by decide +kernel
theorem atom0271Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159127418419200 : Int) atom0271Coded) := by
  have h := atom0271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0272 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0272 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161168603904000 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272Coded : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 1))]
theorem atom0272Coded_decode : atom0272 = SparsePolynomial.decodeCubic 24 atom0272Coded := by decide +kernel
theorem atom0272Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161168603904000 : Int) atom0272Coded) := by
  have h := atom0272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0273 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0273 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183818320963200 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273Coded : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 1))]
theorem atom0273Coded_decode : atom0273 = SparsePolynomial.decodeCubic 24 atom0273Coded := by decide +kernel
theorem atom0273Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183818320963200 : Int) atom0273Coded) := by
  have h := atom0273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0274 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0274 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104477866416000 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274Coded : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 1))]
theorem atom0274Coded_decode : atom0274 = SparsePolynomial.decodeCubic 24 atom0274Coded := by decide +kernel
theorem atom0274Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104477866416000 : Int) atom0274Coded) := by
  have h := atom0274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0275 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0275 = ((g 0) * (g 2) * (g 20)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90763651440000 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275Coded : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 1))]
theorem atom0275Coded_decode : atom0275 = SparsePolynomial.decodeCubic 24 atom0275Coded := by decide +kernel
theorem atom0275Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90763651440000 : Int) atom0275Coded) := by
  have h := atom0275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0276 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0276 = ((g 0) * (g 2) * (g 21)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11423196892800 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276Coded : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 1))]
theorem atom0276Coded_decode : atom0276 = SparsePolynomial.decodeCubic 24 atom0276Coded := by decide +kernel
theorem atom0276Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11423196892800 : Int) atom0276Coded) := by
  have h := atom0276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0277 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0277 = ((g 0) * (g 2) * (g 22)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20816644867200 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 2) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277Coded : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 1))]
theorem atom0277Coded_decode : atom0277 = SparsePolynomial.decodeCubic 24 atom0277Coded := by decide +kernel
theorem atom0277Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20816644867200 : Int) atom0277Coded) := by
  have h := atom0277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0278 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0278 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64233555724800 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278Coded : CoefficientMerge.Poly := [(nat_lit 75, Int.ofNat (nat_lit 1))]
theorem atom0278Coded_decode : atom0278 = SparsePolynomial.decodeCubic 24 atom0278Coded := by decide +kernel
theorem atom0278Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (64233555724800 : Int) atom0278Coded) := by
  have h := atom0278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0279 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0279 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131528889676800 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279Coded : CoefficientMerge.Poly := [(nat_lit 76, Int.ofNat (nat_lit 1))]
theorem atom0279Coded_decode : atom0279 = SparsePolynomial.decodeCubic 24 atom0279Coded := by decide +kernel
theorem atom0279Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131528889676800 : Int) atom0279Coded) := by
  have h := atom0279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0280 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0280 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134590667904000 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280Coded : CoefficientMerge.Poly := [(nat_lit 77, Int.ofNat (nat_lit 1))]
theorem atom0280Coded_decode : atom0280 = SparsePolynomial.decodeCubic 24 atom0280Coded := by decide +kernel
theorem atom0280Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134590667904000 : Int) atom0280Coded) := by
  have h := atom0280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0281 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0281 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137652446131200 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281Coded : CoefficientMerge.Poly := [(nat_lit 78, Int.ofNat (nat_lit 1))]
theorem atom0281Coded_decode : atom0281 = SparsePolynomial.decodeCubic 24 atom0281Coded := by decide +kernel
theorem atom0281Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137652446131200 : Int) atom0281Coded) := by
  have h := atom0281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0282 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0282 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140714224358400 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282Coded : CoefficientMerge.Poly := [(nat_lit 79, Int.ofNat (nat_lit 1))]
theorem atom0282Coded_decode : atom0282 = SparsePolynomial.decodeCubic 24 atom0282Coded := by decide +kernel
theorem atom0282Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140714224358400 : Int) atom0282Coded) := by
  have h := atom0282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0283 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0283 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143776002585600 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283Coded : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 1))]
theorem atom0283Coded_decode : atom0283 = SparsePolynomial.decodeCubic 24 atom0283Coded := by decide +kernel
theorem atom0283Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143776002585600 : Int) atom0283Coded) := by
  have h := atom0283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0284 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0284 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146837780812800 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284Coded : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 1))]
theorem atom0284Coded_decode : atom0284 = SparsePolynomial.decodeCubic 24 atom0284Coded := by decide +kernel
theorem atom0284Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146837780812800 : Int) atom0284Coded) := by
  have h := atom0284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0285 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0285 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149899559040000 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285Coded : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 1))]
theorem atom0285Coded_decode : atom0285 = SparsePolynomial.decodeCubic 24 atom0285Coded := by decide +kernel
theorem atom0285Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149899559040000 : Int) atom0285Coded) := by
  have h := atom0285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0286 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0286 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157608664031808 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286Coded : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 1))]
theorem atom0286Coded_decode : atom0286 = SparsePolynomial.decodeCubic 24 atom0286Coded := by decide +kernel
theorem atom0286Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157608664031808 : Int) atom0286Coded) := by
  have h := atom0286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0287 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0287 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210348325554048 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287Coded : CoefficientMerge.Poly := [(nat_lit 84, Int.ofNat (nat_lit 1))]
theorem atom0287Coded_decode : atom0287 = SparsePolynomial.decodeCubic 24 atom0287Coded := by decide +kernel
theorem atom0287Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210348325554048 : Int) atom0287Coded) := by
  have h := atom0287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0288 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0288 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189921761568000 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288Coded : CoefficientMerge.Poly := [(nat_lit 85, Int.ofNat (nat_lit 1))]
theorem atom0288Coded_decode : atom0288 = SparsePolynomial.decodeCubic 24 atom0288Coded := by decide +kernel
theorem atom0288Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189921761568000 : Int) atom0288Coded) := by
  have h := atom0288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block005 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 2323663382304)), (nat_lit 12, Int.ofNat (nat_lit 27162605029824)), (nat_lit 13, Int.ofNat (nat_lit 15418433923200)), (nat_lit 18, Int.ofNat (nat_lit 11502930700800)), (nat_lit 19, Int.ofNat (nat_lit 8419890124800)), (nat_lit 20, Int.ofNat (nat_lit 5336849548800)), (nat_lit 21, Int.ofNat (nat_lit 2253808972800)), (nat_lit 25, Int.ofNat (nat_lit 2338858368000)), (nat_lit 26, Int.ofNat (nat_lit 60480751161600)), (nat_lit 27, Int.ofNat (nat_lit 59959823616000)), (nat_lit 28, Int.ofNat (nat_lit 59438896070400)), (nat_lit 29, Int.ofNat (nat_lit 62359415395200)), (nat_lit 30, Int.ofNat (nat_lit 58397040979200)), (nat_lit 31, Int.ofNat (nat_lit 57876113433600)), (nat_lit 32, Int.ofNat (nat_lit 57355185888000)), (nat_lit 33, Int.ofNat (nat_lit 59840148865464)), (nat_lit 34, Int.ofNat (nat_lit 68140969836984)), (nat_lit 35, Int.ofNat (nat_lit 79108072262208)), (nat_lit 36, Int.ofNat (nat_lit 129806548299648)), (nat_lit 37, Int.ofNat (nat_lit 107338798828800)), (nat_lit 38, Int.ofNat (nat_lit 77522523724800)), (nat_lit 39, Int.ofNat (nat_lit 78227402803200)), (nat_lit 40, Int.ofNat (nat_lit 73021026758400)), (nat_lit 41, Int.ofNat (nat_lit 72781019942400)), (nat_lit 42, Int.ofNat (nat_lit 102984186412800)), (nat_lit 43, Int.ofNat (nat_lit 40961914963200)), (nat_lit 44, Int.ofNat (nat_lit 12512892268800)), (nat_lit 45, Int.ofNat (nat_lit 5205731731200)), (nat_lit 46, Int.ofNat (nat_lit 4086988550400)), (nat_lit 50, Int.ofNat (nat_lit 65275410816000)), (nat_lit 51, Int.ofNat (nat_lit 132592007116800)), (nat_lit 52, Int.ofNat (nat_lit 134633192601600)), (nat_lit 53, Int.ofNat (nat_lit 136674378086400)), (nat_lit 54, Int.ofNat (nat_lit 138715563571200)), (nat_lit 55, Int.ofNat (nat_lit 140756749056000)), (nat_lit 56, Int.ofNat (nat_lit 142797934540800)), (nat_lit 57, Int.ofNat (nat_lit 144839120025600)), (nat_lit 58, Int.ofNat (nat_lit 146880305510400)), (nat_lit 59, Int.ofNat (nat_lit 153568817759808)), (nat_lit 60, Int.ofNat (nat_lit 205287886539648)), (nat_lit 61, Int.ofNat (nat_lit 183840729811200)), (nat_lit 62, Int.ofNat (nat_lit 155045047449600)), (nat_lit 63, Int.ofNat (nat_lit 157086232934400)), (nat_lit 64, Int.ofNat (nat_lit 159127418419200)), (nat_lit 65, Int.ofNat (nat_lit 161168603904000)), (nat_lit 66, Int.ofNat (nat_lit 183818320963200)), (nat_lit 67, Int.ofNat (nat_lit 104477866416000)), (nat_lit 68, Int.ofNat (nat_lit 90763651440000)), (nat_lit 69, Int.ofNat (nat_lit 11423196892800)), (nat_lit 70, Int.ofNat (nat_lit 20816644867200)), (nat_lit 75, Int.ofNat (nat_lit 64233555724800)), (nat_lit 76, Int.ofNat (nat_lit 131528889676800)), (nat_lit 77, Int.ofNat (nat_lit 134590667904000)), (nat_lit 78, Int.ofNat (nat_lit 137652446131200)), (nat_lit 79, Int.ofNat (nat_lit 140714224358400)), (nat_lit 80, Int.ofNat (nat_lit 143776002585600)), (nat_lit 81, Int.ofNat (nat_lit 146837780812800)), (nat_lit 82, Int.ofNat (nat_lit 149899559040000)), (nat_lit 83, Int.ofNat (nat_lit 157608664031808)), (nat_lit 84, Int.ofNat (nat_lit 210348325554048)), (nat_lit 85, Int.ofNat (nat_lit 189921761568000)), (nat_lit 252, Int.negSucc (nat_lit 4473274189823)), (nat_lit 275, Int.negSucc (nat_lit 20576091305087)), (nat_lit 276, Int.negSucc (nat_lit 56738800521215)), (nat_lit 277, Int.negSucc (nat_lit 13409545171967)), (nat_lit 300, Int.negSucc (nat_lit 49750818213887)), (nat_lit 301, Int.negSucc (nat_lit 51341575431167)), (nat_lit 302, Int.negSucc (nat_lit 4500641870207)), (nat_lit 325, Int.negSucc (nat_lit 56668745548799)), (nat_lit 326, Int.negSucc (nat_lit 61665751889279)), (nat_lit 327, Int.negSucc (nat_lit 5424680862719)), (nat_lit 350, Int.negSucc (nat_lit 60074994671999)), (nat_lit 351, Int.negSucc (nat_lit 59078112670079)), (nat_lit 352, Int.negSucc (nat_lit 1609463157119)), (nat_lit 375, Int.negSucc (nat_lit 54081106329599)), (nat_lit 376, Int.negSucc (nat_lit 45862757498879)), (nat_lit 400, Int.negSucc (nat_lit 46859639500799)), (nat_lit 401, Int.negSucc (nat_lit 18606058598399)), (nat_lit 425, Int.negSucc (nat_lit 30787881062399)), (nat_lit 475, Int.negSucc (nat_lit 4898845163519)), (nat_lit 828, Int.negSucc (nat_lit 6709911284735)), (nat_lit 851, Int.negSucc (nat_lit 30864136957631)), (nat_lit 852, Int.negSucc (nat_lit 85108200781823)), (nat_lit 853, Int.negSucc (nat_lit 20114317757951)), (nat_lit 876, Int.negSucc (nat_lit 74626227320831)), (nat_lit 877, Int.negSucc (nat_lit 77012363146751)), (nat_lit 878, Int.negSucc (nat_lit 6750962805311)), (nat_lit 901, Int.negSucc (nat_lit 85003118323199)), (nat_lit 902, Int.negSucc (nat_lit 92498627833919)), (nat_lit 903, Int.negSucc (nat_lit 8137021294079)), (nat_lit 926, Int.negSucc (nat_lit 90112492007999)), (nat_lit 927, Int.negSucc (nat_lit 88617169005119)), (nat_lit 928, Int.negSucc (nat_lit 2414194735679)), (nat_lit 951, Int.negSucc (nat_lit 81121659494399)), (nat_lit 952, Int.negSucc (nat_lit 68794136248319)), (nat_lit 976, Int.negSucc (nat_lit 70289459251199)), (nat_lit 977, Int.negSucc (nat_lit 27909087897599)), (nat_lit 1001, Int.negSucc (nat_lit 46181821593599)), (nat_lit 1051, Int.negSucc (nat_lit 7348267745279)), (nat_lit 1404, Int.negSucc (nat_lit 8946548379647)), (nat_lit 1427, Int.negSucc (nat_lit 41152182610175)), (nat_lit 1428, Int.negSucc (nat_lit 113477601042431)), (nat_lit 1429, Int.negSucc (nat_lit 26819090343935)), (nat_lit 1452, Int.negSucc (nat_lit 99501636427775)), (nat_lit 1453, Int.negSucc (nat_lit 102683150862335)), (nat_lit 1454, Int.negSucc (nat_lit 9001283740415)), (nat_lit 1477, Int.negSucc (nat_lit 113337491097599)), (nat_lit 1478, Int.negSucc (nat_lit 123331503778559)), (nat_lit 1479, Int.negSucc (nat_lit 10849361725439)), (nat_lit 1502, Int.negSucc (nat_lit 120149989343999)), (nat_lit 1503, Int.negSucc (nat_lit 118156225340159)), (nat_lit 1504, Int.negSucc (nat_lit 3218926314239)), (nat_lit 1527, Int.negSucc (nat_lit 108162212659199)), (nat_lit 1528, Int.negSucc (nat_lit 91725514997759)), (nat_lit 1552, Int.negSucc (nat_lit 93719279001599)), (nat_lit 1553, Int.negSucc (nat_lit 37212117196799)), (nat_lit 1577, Int.negSucc (nat_lit 61575762124799)), (nat_lit 1627, Int.negSucc (nat_lit 9797690327039)), (nat_lit 1980, Int.negSucc (nat_lit 8946548379647)), (nat_lit 2003, Int.negSucc (nat_lit 41152182610175)), (nat_lit 2004, Int.negSucc (nat_lit 113477601042431)), (nat_lit 2005, Int.negSucc (nat_lit 26819090343935)), (nat_lit 2028, Int.negSucc (nat_lit 99501636427775)), (nat_lit 2029, Int.negSucc (nat_lit 102683150862335)), (nat_lit 2030, Int.negSucc (nat_lit 9001283740415)), (nat_lit 2053, Int.negSucc (nat_lit 113337491097599)), (nat_lit 2054, Int.negSucc (nat_lit 123331503778559)), (nat_lit 2055, Int.negSucc (nat_lit 10849361725439)), (nat_lit 2078, Int.negSucc (nat_lit 120149989343999)), (nat_lit 2079, Int.negSucc (nat_lit 118156225340159)), (nat_lit 2080, Int.negSucc (nat_lit 3218926314239)), (nat_lit 2103, Int.negSucc (nat_lit 108162212659199)), (nat_lit 2104, Int.negSucc (nat_lit 91725514997759)), (nat_lit 2128, Int.negSucc (nat_lit 93719279001599)), (nat_lit 2129, Int.negSucc (nat_lit 37212117196799)), (nat_lit 2153, Int.negSucc (nat_lit 61575762124799)), (nat_lit 2203, Int.negSucc (nat_lit 9797690327039)), (nat_lit 2556, Int.negSucc (nat_lit 8946548379647)), (nat_lit 2579, Int.negSucc (nat_lit 41152182610175)), (nat_lit 2580, Int.negSucc (nat_lit 113477601042431)), (nat_lit 2581, Int.negSucc (nat_lit 26819090343935)), (nat_lit 2604, Int.negSucc (nat_lit 99501636427775)), (nat_lit 2605, Int.negSucc (nat_lit 102683150862335)), (nat_lit 2606, Int.negSucc (nat_lit 9001283740415)), (nat_lit 2629, Int.negSucc (nat_lit 113337491097599)), (nat_lit 2630, Int.negSucc (nat_lit 123331503778559)), (nat_lit 2631, Int.negSucc (nat_lit 10849361725439)), (nat_lit 2654, Int.negSucc (nat_lit 120149989343999)), (nat_lit 2655, Int.negSucc (nat_lit 118156225340159)), (nat_lit 2656, Int.negSucc (nat_lit 3218926314239)), (nat_lit 2679, Int.negSucc (nat_lit 108162212659199)), (nat_lit 2680, Int.negSucc (nat_lit 91725514997759)), (nat_lit 2704, Int.negSucc (nat_lit 93719279001599)), (nat_lit 2705, Int.negSucc (nat_lit 37212117196799)), (nat_lit 2729, Int.negSucc (nat_lit 61575762124799)), (nat_lit 2779, Int.negSucc (nat_lit 9797690327039)), (nat_lit 3132, Int.negSucc (nat_lit 8946548379647)), (nat_lit 3155, Int.negSucc (nat_lit 41152182610175)), (nat_lit 3156, Int.negSucc (nat_lit 113477601042431)), (nat_lit 3157, Int.negSucc (nat_lit 26819090343935)), (nat_lit 3180, Int.negSucc (nat_lit 99501636427775)), (nat_lit 3181, Int.negSucc (nat_lit 102683150862335)), (nat_lit 3182, Int.negSucc (nat_lit 9001283740415)), (nat_lit 3205, Int.negSucc (nat_lit 113337491097599)), (nat_lit 3206, Int.negSucc (nat_lit 123331503778559)), (nat_lit 3207, Int.negSucc (nat_lit 10849361725439)), (nat_lit 3230, Int.negSucc (nat_lit 120149989343999)), (nat_lit 3231, Int.negSucc (nat_lit 118156225340159)), (nat_lit 3232, Int.negSucc (nat_lit 3218926314239)), (nat_lit 3255, Int.negSucc (nat_lit 108162212659199)), (nat_lit 3256, Int.negSucc (nat_lit 91725514997759)), (nat_lit 3280, Int.negSucc (nat_lit 93719279001599)), (nat_lit 3281, Int.negSucc (nat_lit 37212117196799)), (nat_lit 3305, Int.negSucc (nat_lit 61575762124799)), (nat_lit 3355, Int.negSucc (nat_lit 9797690327039)), (nat_lit 3708, Int.negSucc (nat_lit 8946548379647)), (nat_lit 3731, Int.negSucc (nat_lit 41152182610175)), (nat_lit 3732, Int.negSucc (nat_lit 113477601042431)), (nat_lit 3733, Int.negSucc (nat_lit 26819090343935)), (nat_lit 3756, Int.negSucc (nat_lit 99501636427775)), (nat_lit 3757, Int.negSucc (nat_lit 102683150862335)), (nat_lit 3758, Int.negSucc (nat_lit 9001283740415)), (nat_lit 3781, Int.negSucc (nat_lit 113337491097599)), (nat_lit 3782, Int.negSucc (nat_lit 123331503778559)), (nat_lit 3783, Int.negSucc (nat_lit 10849361725439)), (nat_lit 3806, Int.negSucc (nat_lit 120149989343999)), (nat_lit 3807, Int.negSucc (nat_lit 118156225340159)), (nat_lit 3808, Int.negSucc (nat_lit 3218926314239)), (nat_lit 3831, Int.negSucc (nat_lit 108162212659199)), (nat_lit 3832, Int.negSucc (nat_lit 91725514997759)), (nat_lit 3856, Int.negSucc (nat_lit 93719279001599)), (nat_lit 3857, Int.negSucc (nat_lit 37212117196799)), (nat_lit 3881, Int.negSucc (nat_lit 61575762124799)), (nat_lit 3931, Int.negSucc (nat_lit 9797690327039)), (nat_lit 4284, Int.negSucc (nat_lit 8946548379647)), (nat_lit 4307, Int.negSucc (nat_lit 41152182610175)), (nat_lit 4308, Int.negSucc (nat_lit 113477601042431)), (nat_lit 4309, Int.negSucc (nat_lit 26819090343935)), (nat_lit 4332, Int.negSucc (nat_lit 99501636427775)), (nat_lit 4333, Int.negSucc (nat_lit 102683150862335)), (nat_lit 4334, Int.negSucc (nat_lit 9001283740415)), (nat_lit 4357, Int.negSucc (nat_lit 113337491097599)), (nat_lit 4358, Int.negSucc (nat_lit 123331503778559)), (nat_lit 4359, Int.negSucc (nat_lit 10849361725439)), (nat_lit 4382, Int.negSucc (nat_lit 120149989343999)), (nat_lit 4383, Int.negSucc (nat_lit 118156225340159)), (nat_lit 4384, Int.negSucc (nat_lit 3218926314239)), (nat_lit 4407, Int.negSucc (nat_lit 108162212659199)), (nat_lit 4408, Int.negSucc (nat_lit 91725514997759)), (nat_lit 4432, Int.negSucc (nat_lit 93719279001599)), (nat_lit 4433, Int.negSucc (nat_lit 37212117196799)), (nat_lit 4457, Int.negSucc (nat_lit 61575762124799)), (nat_lit 4507, Int.negSucc (nat_lit 9797690327039)), (nat_lit 4860, Int.negSucc (nat_lit 8946548379647)), (nat_lit 4883, Int.negSucc (nat_lit 41152182610175)), (nat_lit 4884, Int.negSucc (nat_lit 113477601042431)), (nat_lit 4885, Int.negSucc (nat_lit 26819090343935)), (nat_lit 4908, Int.negSucc (nat_lit 99501636427775)), (nat_lit 4909, Int.negSucc (nat_lit 102683150862335)), (nat_lit 4910, Int.negSucc (nat_lit 9001283740415)), (nat_lit 4933, Int.negSucc (nat_lit 113337491097599)), (nat_lit 4934, Int.negSucc (nat_lit 123331503778559)), (nat_lit 4935, Int.negSucc (nat_lit 10849361725439)), (nat_lit 4958, Int.negSucc (nat_lit 120149989343999)), (nat_lit 4959, Int.negSucc (nat_lit 118156225340159)), (nat_lit 4960, Int.negSucc (nat_lit 3218926314239)), (nat_lit 4983, Int.negSucc (nat_lit 108162212659199)), (nat_lit 4984, Int.negSucc (nat_lit 91725514997759)), (nat_lit 5008, Int.negSucc (nat_lit 93719279001599)), (nat_lit 5009, Int.negSucc (nat_lit 37212117196799)), (nat_lit 5033, Int.negSucc (nat_lit 61575762124799)), (nat_lit 5083, Int.negSucc (nat_lit 9797690327039)), (nat_lit 5436, Int.negSucc (nat_lit 8946548379647)), (nat_lit 5459, Int.negSucc (nat_lit 41152182610175)), (nat_lit 5460, Int.negSucc (nat_lit 113477601042431)), (nat_lit 5461, Int.negSucc (nat_lit 26819090343935)), (nat_lit 5484, Int.negSucc (nat_lit 99501636427775)), (nat_lit 5485, Int.negSucc (nat_lit 102683150862335)), (nat_lit 5486, Int.negSucc (nat_lit 9001283740415)), (nat_lit 5509, Int.negSucc (nat_lit 113337491097599)), (nat_lit 5510, Int.negSucc (nat_lit 123331503778559)), (nat_lit 5511, Int.negSucc (nat_lit 10849361725439)), (nat_lit 5534, Int.negSucc (nat_lit 120149989343999)), (nat_lit 5535, Int.negSucc (nat_lit 118156225340159)), (nat_lit 5536, Int.negSucc (nat_lit 3218926314239)), (nat_lit 5559, Int.negSucc (nat_lit 108162212659199)), (nat_lit 5560, Int.negSucc (nat_lit 91725514997759)), (nat_lit 5584, Int.negSucc (nat_lit 93719279001599)), (nat_lit 5585, Int.negSucc (nat_lit 37212117196799)), (nat_lit 5609, Int.negSucc (nat_lit 61575762124799)), (nat_lit 5659, Int.negSucc (nat_lit 9797690327039)), (nat_lit 6012, Int.negSucc (nat_lit 8946548379647)), (nat_lit 6035, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6036, Int.negSucc (nat_lit 122424149422079)), (nat_lit 6037, Int.negSucc (nat_lit 26819090343935)), (nat_lit 6060, Int.negSucc (nat_lit 108448184807423)), (nat_lit 6061, Int.negSucc (nat_lit 111629699241983)), (nat_lit 6062, Int.negSucc (nat_lit 17947832120063)), (nat_lit 6063, Int.negSucc (nat_lit 8946548379647)), (nat_lit 6064, Int.negSucc (nat_lit 8946548379647)), (nat_lit 6065, Int.negSucc (nat_lit 8946548379647)), (nat_lit 6066, Int.negSucc (nat_lit 7828229832191)), (nat_lit 6067, Int.negSucc (nat_lit 5591592737279)), (nat_lit 6068, Int.negSucc (nat_lit 1118318547455)), (nat_lit 6069, Int.ofNat (nat_lit 1118318547456)), (nat_lit 6070, Int.ofNat (nat_lit 5591592737280)), (nat_lit 6071, Int.ofNat (nat_lit 10064866927104)), (nat_lit 6085, Int.negSucc (nat_lit 113337491097599)), (nat_lit 6086, Int.negSucc (nat_lit 123331503778559)), (nat_lit 6087, Int.negSucc (nat_lit 10849361725439)), (nat_lit 6110, Int.negSucc (nat_lit 120149989343999)), (nat_lit 6111, Int.negSucc (nat_lit 118156225340159)), (nat_lit 6112, Int.negSucc (nat_lit 3218926314239)), (nat_lit 6135, Int.negSucc (nat_lit 108162212659199)), (nat_lit 6136, Int.negSucc (nat_lit 91725514997759)), (nat_lit 6160, Int.negSucc (nat_lit 93719279001599)), (nat_lit 6161, Int.negSucc (nat_lit 37212117196799)), (nat_lit 6185, Int.negSucc (nat_lit 61575762124799)), (nat_lit 6235, Int.negSucc (nat_lit 9797690327039)), (nat_lit 6611, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6612, Int.negSucc (nat_lit 154629783652607)), (nat_lit 6613, Int.negSucc (nat_lit 67971272954111)), (nat_lit 6614, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6615, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6616, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6617, Int.negSucc (nat_lit 41152182610175)), (nat_lit 6618, Int.negSucc (nat_lit 36008159783903)), (nat_lit 6619, Int.negSucc (nat_lit 25720114131359)), (nat_lit 6620, Int.negSucc (nat_lit 5144022826271)), (nat_lit 6621, Int.ofNat (nat_lit 5144022826272)), (nat_lit 6622, Int.ofNat (nat_lit 25720114131360)), (nat_lit 6623, Int.ofNat (nat_lit 46296205436448)), (nat_lit 6636, Int.negSucc (nat_lit 212979237470207)), (nat_lit 6637, Int.negSucc (nat_lit 242979842248703)), (nat_lit 6638, Int.negSucc (nat_lit 122478884782847)), (nat_lit 6639, Int.negSucc (nat_lit 113477601042431)), (nat_lit 6640, Int.negSucc (nat_lit 113477601042431)), (nat_lit 6641, Int.negSucc (nat_lit 113477601042431)), (nat_lit 6642, Int.negSucc (nat_lit 99292900912127)), (nat_lit 6643, Int.negSucc (nat_lit 70923500651519)), (nat_lit 6644, Int.negSucc (nat_lit 14184700130303)), (nat_lit 6645, Int.ofNat (nat_lit 14184700130304)), (nat_lit 6646, Int.ofNat (nat_lit 70923500651520)), (nat_lit 6647, Int.ofNat (nat_lit 127662301172736)), (nat_lit 6661, Int.negSucc (nat_lit 140156581441535)), (nat_lit 6662, Int.negSucc (nat_lit 150150594122495)), (nat_lit 6663, Int.negSucc (nat_lit 37668452069375)), (nat_lit 6664, Int.negSucc (nat_lit 26819090343935)), (nat_lit 6665, Int.negSucc (nat_lit 26819090343935)), (nat_lit 6666, Int.negSucc (nat_lit 23466704050943)), (nat_lit 6667, Int.negSucc (nat_lit 16761931464959)), (nat_lit 6668, Int.negSucc (nat_lit 3352386292991)), (nat_lit 6669, Int.ofNat (nat_lit 3352386292992)), (nat_lit 6670, Int.ofNat (nat_lit 16761931464960)), (nat_lit 6671, Int.ofNat (nat_lit 30171476636928)), (nat_lit 6686, Int.negSucc (nat_lit 120149989343999)), (nat_lit 6687, Int.negSucc (nat_lit 118156225340159)), (nat_lit 6688, Int.negSucc (nat_lit 3218926314239)), (nat_lit 6711, Int.negSucc (nat_lit 108162212659199)), (nat_lit 6712, Int.negSucc (nat_lit 91725514997759)), (nat_lit 6736, Int.negSucc (nat_lit 93719279001599)), (nat_lit 6737, Int.negSucc (nat_lit 37212117196799)), (nat_lit 6761, Int.negSucc (nat_lit 61575762124799)), (nat_lit 6811, Int.negSucc (nat_lit 9797690327039)), (nat_lit 7212, Int.negSucc (nat_lit 99501636427775)), (nat_lit 7213, Int.negSucc (nat_lit 202184787290111)), (nat_lit 7214, Int.negSucc (nat_lit 108502920168191)), (nat_lit 7215, Int.negSucc (nat_lit 99501636427775)), (nat_lit 7216, Int.negSucc (nat_lit 99501636427775)), (nat_lit 7217, Int.negSucc (nat_lit 99501636427775)), (nat_lit 7218, Int.negSucc (nat_lit 87063931874303)), (nat_lit 7219, Int.negSucc (nat_lit 62188522767359)), (nat_lit 7220, Int.negSucc (nat_lit 12437704553471)), (nat_lit 7221, Int.ofNat (nat_lit 12437704553472)), (nat_lit 7222, Int.ofNat (nat_lit 62188522767360)), (nat_lit 7223, Int.ofNat (nat_lit 111939340981248)), (nat_lit 7237, Int.negSucc (nat_lit 216020641959935)), (nat_lit 7238, Int.negSucc (nat_lit 235015938381311)), (nat_lit 7239, Int.negSucc (nat_lit 113532512587775)), (nat_lit 7240, Int.negSucc (nat_lit 102683150862335)), (nat_lit 7241, Int.negSucc (nat_lit 102683150862335)), (nat_lit 7242, Int.negSucc (nat_lit 89847757004543)), (nat_lit 7243, Int.negSucc (nat_lit 64176969288959)), (nat_lit 7244, Int.negSucc (nat_lit 12835393857791)), (nat_lit 7245, Int.ofNat (nat_lit 12835393857792)), (nat_lit 7246, Int.ofNat (nat_lit 64176969288960)), (nat_lit 7247, Int.ofNat (nat_lit 115518544720128)), (nat_lit 7262, Int.negSucc (nat_lit 129151273084415)), (nat_lit 7263, Int.negSucc (nat_lit 127157509080575)), (nat_lit 7264, Int.negSucc (nat_lit 12220210054655)), (nat_lit 7265, Int.negSucc (nat_lit 9001283740415)), (nat_lit 7266, Int.negSucc (nat_lit 7876123272863)), (nat_lit 7267, Int.negSucc (nat_lit 5625802337759)), (nat_lit 7268, Int.negSucc (nat_lit 1125160467551)), (nat_lit 7269, Int.ofNat (nat_lit 1125160467552)), (nat_lit 7270, Int.ofNat (nat_lit 5625802337760)), (nat_lit 7271, Int.ofNat (nat_lit 10126444207968)), (nat_lit 7287, Int.negSucc (nat_lit 108162212659199)), (nat_lit 7288, Int.negSucc (nat_lit 91725514997759)), (nat_lit 7312, Int.negSucc (nat_lit 93719279001599)), (nat_lit 7313, Int.negSucc (nat_lit 37212117196799)), (nat_lit 7337, Int.negSucc (nat_lit 61575762124799)), (nat_lit 7387, Int.negSucc (nat_lit 9797690327039)), (nat_lit 7813, Int.negSucc (nat_lit 113337491097599)), (nat_lit 7814, Int.negSucc (nat_lit 236668994876159)), (nat_lit 7815, Int.negSucc (nat_lit 124186852823039)), (nat_lit 7816, Int.negSucc (nat_lit 113337491097599)), (nat_lit 7817, Int.negSucc (nat_lit 113337491097599)), (nat_lit 7818, Int.negSucc (nat_lit 99170304710399)), (nat_lit 7819, Int.negSucc (nat_lit 70835931935999)), (nat_lit 7820, Int.negSucc (nat_lit 14167186387199)), (nat_lit 7821, Int.ofNat (nat_lit 14167186387200)), (nat_lit 7822, Int.ofNat (nat_lit 70835931936000)), (nat_lit 7823, Int.ofNat (nat_lit 127504677484800)), (nat_lit 7838, Int.negSucc (nat_lit 243481493122559)), (nat_lit 7839, Int.negSucc (nat_lit 252337090844159)), (nat_lit 7840, Int.negSucc (nat_lit 126550430092799)), (nat_lit 7841, Int.negSucc (nat_lit 123331503778559)), (nat_lit 7842, Int.negSucc (nat_lit 107915065806239)), (nat_lit 7843, Int.negSucc (nat_lit 77082189861599)), (nat_lit 7844, Int.negSucc (nat_lit 15416437972319)), (nat_lit 7845, Int.ofNat (nat_lit 15416437972320)), (nat_lit 7846, Int.ofNat (nat_lit 77082189861600)), (nat_lit 7847, Int.ofNat (nat_lit 138747941750880)), (nat_lit 7863, Int.negSucc (nat_lit 119011574384639)), (nat_lit 7864, Int.negSucc (nat_lit 102574876723199)), (nat_lit 7865, Int.negSucc (nat_lit 10849361725439)), (nat_lit 7866, Int.negSucc (nat_lit 9493191509759)), (nat_lit 7867, Int.negSucc (nat_lit 6780851078399)), (nat_lit 7868, Int.negSucc (nat_lit 1356170215679)), (nat_lit 7869, Int.ofNat (nat_lit 1356170215680)), (nat_lit 7870, Int.ofNat (nat_lit 6780851078400)), (nat_lit 7871, Int.ofNat (nat_lit 12205531941120)), (nat_lit 7888, Int.negSucc (nat_lit 93719279001599)), (nat_lit 7889, Int.negSucc (nat_lit 37212117196799)), (nat_lit 7913, Int.negSucc (nat_lit 61575762124799)), (nat_lit 7963, Int.negSucc (nat_lit 9797690327039)), (nat_lit 8414, Int.negSucc (nat_lit 120149989343999)), (nat_lit 8415, Int.negSucc (nat_lit 238306214684159)), (nat_lit 8416, Int.negSucc (nat_lit 123368915658239)), (nat_lit 8417, Int.negSucc (nat_lit 120149989343999)), (nat_lit 8418, Int.negSucc (nat_lit 105131240675999)), (nat_lit 8419, Int.negSucc (nat_lit 75093743339999)), (nat_lit 8420, Int.negSucc (nat_lit 15018748667999)), (nat_lit 8421, Int.ofNat (nat_lit 15018748668000)), (nat_lit 8422, Int.ofNat (nat_lit 75093743340000)), (nat_lit 8423, Int.ofNat (nat_lit 135168738012000)), (nat_lit 8439, Int.negSucc (nat_lit 226318437999359)), (nat_lit 8440, Int.negSucc (nat_lit 213100666652159)), (nat_lit 8441, Int.negSucc (nat_lit 118156225340159)), (nat_lit 8442, Int.negSucc (nat_lit 103386697172639)), (nat_lit 8443, Int.negSucc (nat_lit 73847640837599)), (nat_lit 8444, Int.negSucc (nat_lit 14769528167519)), (nat_lit 8445, Int.ofNat (nat_lit 14769528167520)), (nat_lit 8446, Int.ofNat (nat_lit 73847640837600)), (nat_lit 8447, Int.ofNat (nat_lit 132925753507680)), (nat_lit 8464, Int.negSucc (nat_lit 96938205315839)), (nat_lit 8465, Int.negSucc (nat_lit 40431043511039)), (nat_lit 8466, Int.negSucc (nat_lit 2816560524959)), (nat_lit 8467, Int.negSucc (nat_lit 2011828946399)), (nat_lit 8468, Int.negSucc (nat_lit 402365789279)), (nat_lit 8469, Int.ofNat (nat_lit 402365789280)), (nat_lit 8470, Int.ofNat (nat_lit 2011828946400)), (nat_lit 8471, Int.ofNat (nat_lit 3621292103520)), (nat_lit 8489, Int.negSucc (nat_lit 61575762124799)), (nat_lit 8539, Int.negSucc (nat_lit 9797690327039)), (nat_lit 9015, Int.negSucc (nat_lit 108162212659199)), (nat_lit 9016, Int.negSucc (nat_lit 199887727656959)), (nat_lit 9017, Int.negSucc (nat_lit 108162212659199)), (nat_lit 9018, Int.negSucc (nat_lit 94641936076799)), (nat_lit 9019, Int.negSucc (nat_lit 67601382911999)), (nat_lit 9020, Int.negSucc (nat_lit 13520276582399)), (nat_lit 9021, Int.ofNat (nat_lit 13520276582400)), (nat_lit 9022, Int.ofNat (nat_lit 67601382912000)), (nat_lit 9023, Int.ofNat (nat_lit 121682489241600)), (nat_lit 9040, Int.negSucc (nat_lit 185444793999359)), (nat_lit 9041, Int.negSucc (nat_lit 128937632194559)), (nat_lit 9042, Int.negSucc (nat_lit 80259825623039)), (nat_lit 9043, Int.negSucc (nat_lit 57328446873599)), (nat_lit 9044, Int.negSucc (nat_lit 11465689374719)), (nat_lit 9045, Int.ofNat (nat_lit 11465689374720)), (nat_lit 9046, Int.ofNat (nat_lit 57328446873600)), (nat_lit 9047, Int.ofNat (nat_lit 103191204372480)), (nat_lit 9065, Int.negSucc (nat_lit 61575762124799)), (nat_lit 9115, Int.negSucc (nat_lit 9797690327039)), (nat_lit 9616, Int.negSucc (nat_lit 93719279001599)), (nat_lit 9617, Int.negSucc (nat_lit 130931396198399)), (nat_lit 9618, Int.negSucc (nat_lit 82004369126399)), (nat_lit 9619, Int.negSucc (nat_lit 58574549375999)), (nat_lit 9620, Int.negSucc (nat_lit 11714909875199)), (nat_lit 9621, Int.ofNat (nat_lit 11714909875200)), (nat_lit 9622, Int.ofNat (nat_lit 58574549376000)), (nat_lit 9623, Int.ofNat (nat_lit 105434188876800)), (nat_lit 9641, Int.negSucc (nat_lit 98787879321599)), (nat_lit 9642, Int.negSucc (nat_lit 32560602547199)), (nat_lit 9643, Int.negSucc (nat_lit 23257573247999)), (nat_lit 9644, Int.negSucc (nat_lit 4651514649599)), (nat_lit 9645, Int.ofNat (nat_lit 4651514649600)), (nat_lit 9646, Int.ofNat (nat_lit 23257573248000)), (nat_lit 9647, Int.ofNat (nat_lit 41863631846400)), (nat_lit 9691, Int.negSucc (nat_lit 9797690327039)), (nat_lit 10217, Int.negSucc (nat_lit 61575762124799)), (nat_lit 10218, Int.negSucc (nat_lit 53878791859199)), (nat_lit 10219, Int.negSucc (nat_lit 38484851327999)), (nat_lit 10220, Int.negSucc (nat_lit 7696970265599)), (nat_lit 10221, Int.ofNat (nat_lit 7696970265600)), (nat_lit 10222, Int.ofNat (nat_lit 38484851328000)), (nat_lit 10223, Int.ofNat (nat_lit 69272732390400)), (nat_lit 10267, Int.negSucc (nat_lit 9797690327039)), (nat_lit 10843, Int.negSucc (nat_lit 8572979036159)), (nat_lit 11419, Int.negSucc (nat_lit 6123556454399)), (nat_lit 11420, Int.negSucc (nat_lit 1224711290879)), (nat_lit 11421, Int.ofNat (nat_lit 1224711290880)), (nat_lit 11422, Int.ofNat (nat_lit 6123556454400)), (nat_lit 11423, Int.ofNat (nat_lit 11022401617920))]
theorem block005_data : block005 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (559159273728 : Int) atom0209Coded) (CoefficientMerge.scale (2572011413136 : Int) atom0210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7092350065152 : Int) atom0211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1676193146496 : Int) atom0212Coded) (CoefficientMerge.scale (6218852276736 : Int) atom0213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6417696928896 : Int) atom0214Coded) (CoefficientMerge.scale (562580233776 : Int) atom0215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7083593193600 : Int) atom0216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7708218986160 : Int) atom0217Coded) (CoefficientMerge.scale (678085107840 : Int) atom0218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7509374334000 : Int) atom0219Coded) (CoefficientMerge.scale (7384764083760 : Int) atom0220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201182894640 : Int) atom0221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6760138291200 : Int) atom0222Coded) (CoefficientMerge.scale (5732844687360 : Int) atom0223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5857454937600 : Int) atom0224Coded) (CoefficientMerge.scale (2325757324800 : Int) atom0225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3848485132800 : Int) atom0226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (612355645440 : Int) atom0227Coded) (CoefficientMerge.scale (2323663382304 : Int) atom0228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27162605029824 : Int) atom0229Coded) (CoefficientMerge.scale (15418433923200 : Int) atom0230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11502930700800 : Int) atom0231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8419890124800 : Int) atom0232Coded) (CoefficientMerge.scale (5336849548800 : Int) atom0233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2253808972800 : Int) atom0234Coded) (CoefficientMerge.scale (2338858368000 : Int) atom0235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480751161600 : Int) atom0236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59959823616000 : Int) atom0237Coded) (CoefficientMerge.scale (59438896070400 : Int) atom0238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62359415395200 : Int) atom0239Coded) (CoefficientMerge.scale (58397040979200 : Int) atom0240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57876113433600 : Int) atom0241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57355185888000 : Int) atom0242Coded) (CoefficientMerge.scale (59840148865464 : Int) atom0243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68140969836984 : Int) atom0244Coded) (CoefficientMerge.scale (79108072262208 : Int) atom0245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129806548299648 : Int) atom0246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107338798828800 : Int) atom0247Coded) (CoefficientMerge.scale (77522523724800 : Int) atom0248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78227402803200 : Int) atom0249Coded) (CoefficientMerge.scale (73021026758400 : Int) atom0250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (72781019942400 : Int) atom0251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102984186412800 : Int) atom0252Coded) (CoefficientMerge.scale (40961914963200 : Int) atom0253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512892268800 : Int) atom0254Coded) (CoefficientMerge.scale (5205731731200 : Int) atom0255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4086988550400 : Int) atom0256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65275410816000 : Int) atom0257Coded) (CoefficientMerge.scale (132592007116800 : Int) atom0258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (134633192601600 : Int) atom0259Coded) (CoefficientMerge.scale (136674378086400 : Int) atom0260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (138715563571200 : Int) atom0261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140756749056000 : Int) atom0262Coded) (CoefficientMerge.scale (142797934540800 : Int) atom0263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144839120025600 : Int) atom0264Coded) (CoefficientMerge.scale (146880305510400 : Int) atom0265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153568817759808 : Int) atom0266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (205287886539648 : Int) atom0267Coded) (CoefficientMerge.scale (183840729811200 : Int) atom0268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155045047449600 : Int) atom0269Coded) (CoefficientMerge.scale (157086232934400 : Int) atom0270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159127418419200 : Int) atom0271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161168603904000 : Int) atom0272Coded) (CoefficientMerge.scale (183818320963200 : Int) atom0273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (104477866416000 : Int) atom0274Coded) (CoefficientMerge.scale (90763651440000 : Int) atom0275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11423196892800 : Int) atom0276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20816644867200 : Int) atom0277Coded) (CoefficientMerge.scale (64233555724800 : Int) atom0278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131528889676800 : Int) atom0279Coded) (CoefficientMerge.scale (134590667904000 : Int) atom0280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137652446131200 : Int) atom0281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140714224358400 : Int) atom0282Coded) (CoefficientMerge.scale (143776002585600 : Int) atom0283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146837780812800 : Int) atom0284Coded) (CoefficientMerge.scale (149899559040000 : Int) atom0285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608664031808 : Int) atom0286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210348325554048 : Int) atom0287Coded) (CoefficientMerge.scale (189921761568000 : Int) atom0288Coded)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block005 := by
  rw [block005_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0209Coded_nonneg g hg hA hB) (atom0210Coded_nonneg g hg hA hB)) (add_nonneg (atom0211Coded_nonneg g hg hA hB) (add_nonneg (atom0212Coded_nonneg g hg hA hB) (atom0213Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0214Coded_nonneg g hg hA hB) (atom0215Coded_nonneg g hg hA hB)) (add_nonneg (atom0216Coded_nonneg g hg hA hB) (add_nonneg (atom0217Coded_nonneg g hg hA hB) (atom0218Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0219Coded_nonneg g hg hA hB) (atom0220Coded_nonneg g hg hA hB)) (add_nonneg (atom0221Coded_nonneg g hg hA hB) (add_nonneg (atom0222Coded_nonneg g hg hA hB) (atom0223Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0224Coded_nonneg g hg hA hB) (atom0225Coded_nonneg g hg hA hB)) (add_nonneg (atom0226Coded_nonneg g hg hA hB) (add_nonneg (atom0227Coded_nonneg g hg hA hB) (atom0228Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0229Coded_nonneg g hg hA hB) (atom0230Coded_nonneg g hg hA hB)) (add_nonneg (atom0231Coded_nonneg g hg hA hB) (add_nonneg (atom0232Coded_nonneg g hg hA hB) (atom0233Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0234Coded_nonneg g hg hA hB) (atom0235Coded_nonneg g hg hA hB)) (add_nonneg (atom0236Coded_nonneg g hg hA hB) (add_nonneg (atom0237Coded_nonneg g hg hA hB) (atom0238Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0239Coded_nonneg g hg hA hB) (atom0240Coded_nonneg g hg hA hB)) (add_nonneg (atom0241Coded_nonneg g hg hA hB) (add_nonneg (atom0242Coded_nonneg g hg hA hB) (atom0243Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0244Coded_nonneg g hg hA hB) (atom0245Coded_nonneg g hg hA hB)) (add_nonneg (atom0246Coded_nonneg g hg hA hB) (add_nonneg (atom0247Coded_nonneg g hg hA hB) (atom0248Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0249Coded_nonneg g hg hA hB) (atom0250Coded_nonneg g hg hA hB)) (add_nonneg (atom0251Coded_nonneg g hg hA hB) (add_nonneg (atom0252Coded_nonneg g hg hA hB) (atom0253Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0254Coded_nonneg g hg hA hB) (atom0255Coded_nonneg g hg hA hB)) (add_nonneg (atom0256Coded_nonneg g hg hA hB) (add_nonneg (atom0257Coded_nonneg g hg hA hB) (atom0258Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0259Coded_nonneg g hg hA hB) (atom0260Coded_nonneg g hg hA hB)) (add_nonneg (atom0261Coded_nonneg g hg hA hB) (add_nonneg (atom0262Coded_nonneg g hg hA hB) (atom0263Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0264Coded_nonneg g hg hA hB) (atom0265Coded_nonneg g hg hA hB)) (add_nonneg (atom0266Coded_nonneg g hg hA hB) (add_nonneg (atom0267Coded_nonneg g hg hA hB) (atom0268Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0269Coded_nonneg g hg hA hB) (atom0270Coded_nonneg g hg hA hB)) (add_nonneg (atom0271Coded_nonneg g hg hA hB) (add_nonneg (atom0272Coded_nonneg g hg hA hB) (atom0273Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0274Coded_nonneg g hg hA hB) (atom0275Coded_nonneg g hg hA hB)) (add_nonneg (atom0276Coded_nonneg g hg hA hB) (add_nonneg (atom0277Coded_nonneg g hg hA hB) (atom0278Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0279Coded_nonneg g hg hA hB) (atom0280Coded_nonneg g hg hA hB)) (add_nonneg (atom0281Coded_nonneg g hg hA hB) (add_nonneg (atom0282Coded_nonneg g hg hA hB) (atom0283Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0284Coded_nonneg g hg hA hB) (atom0285Coded_nonneg g hg hA hB)) (add_nonneg (atom0286Coded_nonneg g hg hA hB) (add_nonneg (atom0287Coded_nonneg g hg hA hB) (atom0288Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
