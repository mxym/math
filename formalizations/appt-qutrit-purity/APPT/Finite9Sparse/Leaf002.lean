-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite9Sparse.Base06
import APPT.Finite9Sparse.Base07
import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0160 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 3)), ([nat_lit 1, nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 7)), ([nat_lit 2, nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 15)), ([nat_lit 2, nat_lit 3, nat_lit 7], Int.negSucc (nat_lit 7)), ([nat_lit 2, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 8)), ([nat_lit 2, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 12)), ([nat_lit 2, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 16)), ([nat_lit 2, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0160_data : atom0160 = SparsePolynomial.monoTimes [2,7] 1 base06 := by decide +kernel
theorem eval_atom0160 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = (quadB (outer g) ![1,2,2] * g 2 * g 7) := by
  rw [atom0160_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2565 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(nat_lit 25, Int.negSucc (nat_lit 3)), (nat_lit 106, Int.negSucc (nat_lit 7)), (nat_lit 187, Int.negSucc (nat_lit 15)), (nat_lit 196, Int.negSucc (nat_lit 7)), (nat_lit 214, Int.ofNat (nat_lit 8)), (nat_lit 223, Int.ofNat (nat_lit 12)), (nat_lit 232, Int.ofNat (nat_lit 16)), (nat_lit 233, Int.ofNat (nat_lit 18))]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 9 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (2565 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 1], Int.negSucc (nat_lit 7)), ([nat_lit 0, nat_lit 1, nat_lit 1], Int.negSucc (nat_lit 11)), ([nat_lit 0, nat_lit 1, nat_lit 2], Int.negSucc (nat_lit 15)), ([nat_lit 0, nat_lit 1, nat_lit 3], Int.negSucc (nat_lit 13)), ([nat_lit 0, nat_lit 1, nat_lit 4], Int.negSucc (nat_lit 9)), ([nat_lit 0, nat_lit 1, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 2)), ([nat_lit 0, nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 10)), ([nat_lit 0, nat_lit 1, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0161_data : atom0161 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0161 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0161_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7830 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 7)), (nat_lit 10, Int.negSucc (nat_lit 11)), (nat_lit 11, Int.negSucc (nat_lit 15)), (nat_lit 12, Int.negSucc (nat_lit 13)), (nat_lit 13, Int.negSucc (nat_lit 9)), (nat_lit 14, Int.negSucc (nat_lit 1)), (nat_lit 15, Int.ofNat (nat_lit 2)), (nat_lit 16, Int.ofNat (nat_lit 10)), (nat_lit 17, Int.ofNat (nat_lit 18))]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 9 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (7830 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 2], Int.negSucc (nat_lit 7)), ([nat_lit 0, nat_lit 1, nat_lit 2], Int.negSucc (nat_lit 11)), ([nat_lit 0, nat_lit 2, nat_lit 2], Int.negSucc (nat_lit 15)), ([nat_lit 0, nat_lit 2, nat_lit 3], Int.negSucc (nat_lit 13)), ([nat_lit 0, nat_lit 2, nat_lit 4], Int.negSucc (nat_lit 9)), ([nat_lit 0, nat_lit 2, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 2)), ([nat_lit 0, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 10)), ([nat_lit 0, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0162_data : atom0162 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0162 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0162_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10980 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(nat_lit 2, Int.negSucc (nat_lit 7)), (nat_lit 11, Int.negSucc (nat_lit 11)), (nat_lit 20, Int.negSucc (nat_lit 15)), (nat_lit 21, Int.negSucc (nat_lit 13)), (nat_lit 22, Int.negSucc (nat_lit 9)), (nat_lit 23, Int.negSucc (nat_lit 1)), (nat_lit 24, Int.ofNat (nat_lit 2)), (nat_lit 25, Int.ofNat (nat_lit 10)), (nat_lit 26, Int.ofNat (nat_lit 18))]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 9 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (10980 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 7], Int.negSucc (nat_lit 7)), ([nat_lit 0, nat_lit 1, nat_lit 7], Int.negSucc (nat_lit 11)), ([nat_lit 0, nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 15)), ([nat_lit 0, nat_lit 3, nat_lit 7], Int.negSucc (nat_lit 13)), ([nat_lit 0, nat_lit 4, nat_lit 7], Int.negSucc (nat_lit 9)), ([nat_lit 0, nat_lit 5, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 2)), ([nat_lit 0, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 10)), ([nat_lit 0, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0163_data : atom0163 = SparsePolynomial.monoTimes [0,7] 1 base07 := by decide +kernel
theorem eval_atom0163 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0163_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6930 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(nat_lit 7, Int.negSucc (nat_lit 7)), (nat_lit 16, Int.negSucc (nat_lit 11)), (nat_lit 25, Int.negSucc (nat_lit 15)), (nat_lit 34, Int.negSucc (nat_lit 13)), (nat_lit 43, Int.negSucc (nat_lit 9)), (nat_lit 52, Int.negSucc (nat_lit 1)), (nat_lit 61, Int.ofNat (nat_lit 2)), (nat_lit 70, Int.ofNat (nat_lit 10)), (nat_lit 71, Int.ofNat (nat_lit 18))]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 9 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (6930 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 8], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 1, nat_lit 8], Int.negSucc (nat_lit 11)), ([nat_lit 1, nat_lit 2, nat_lit 8], Int.negSucc (nat_lit 15)), ([nat_lit 1, nat_lit 3, nat_lit 8], Int.negSucc (nat_lit 13)), ([nat_lit 1, nat_lit 4, nat_lit 8], Int.negSucc (nat_lit 9)), ([nat_lit 1, nat_lit 5, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 2)), ([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 10)), ([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0164_data : atom0164 = SparsePolynomial.monoTimes [1,8] 1 base07 := by decide +kernel
theorem eval_atom0164 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = (quadB (outer g) ![2,2,1] * g 1 * g 8) := by
  rw [atom0164_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(nat_lit 17, Int.negSucc (nat_lit 7)), (nat_lit 98, Int.negSucc (nat_lit 11)), (nat_lit 107, Int.negSucc (nat_lit 15)), (nat_lit 116, Int.negSucc (nat_lit 13)), (nat_lit 125, Int.negSucc (nat_lit 9)), (nat_lit 134, Int.negSucc (nat_lit 1)), (nat_lit 143, Int.ofNat (nat_lit 2)), (nat_lit 152, Int.ofNat (nat_lit 10)), (nat_lit 161, Int.ofNat (nat_lit 18))]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 9 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (210 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 13)), ([nat_lit 4, nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 9)), ([nat_lit 4, nat_lit 4, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 2)), ([nat_lit 4, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 10)), ([nat_lit 4, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 18))]
theorem atom0165_data : atom0165 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0165 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0165_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9108 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(nat_lit 40, Int.negSucc (nat_lit 7)), (nat_lit 121, Int.negSucc (nat_lit 11)), (nat_lit 202, Int.negSucc (nat_lit 15)), (nat_lit 283, Int.negSucc (nat_lit 13)), (nat_lit 364, Int.negSucc (nat_lit 9)), (nat_lit 365, Int.negSucc (nat_lit 1)), (nat_lit 366, Int.ofNat (nat_lit 2)), (nat_lit 367, Int.ofNat (nat_lit 10)), (nat_lit 368, Int.ofNat (nat_lit 18))]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 9 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (9108 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block002 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 7, Int.negSucc (nat_lit 55439)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 257039)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.negSucc (nat_lit 4859)), (nat_lit 17, Int.ofNat (nat_lit 139260)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.negSucc (nat_lit 11339)), (nat_lit 26, Int.ofNat (nat_lit 197640)), (nat_lit 34, Int.negSucc (nat_lit 97019)), (nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 43, Int.negSucc (nat_lit 69299)), (nat_lit 52, Int.negSucc (nat_lit 13859)), (nat_lit 61, Int.ofNat (nat_lit 13860)), (nat_lit 70, Int.ofNat (nat_lit 69300)), (nat_lit 71, Int.ofNat (nat_lit 124740)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 106, Int.negSucc (nat_lit 20519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780)), (nat_lit 187, Int.negSucc (nat_lit 41039)), (nat_lit 196, Int.negSucc (nat_lit 20519)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 214, Int.ofNat (nat_lit 20520)), (nat_lit 223, Int.ofNat (nat_lit 30780)), (nat_lit 232, Int.ofNat (nat_lit 41040)), (nat_lit 233, Int.ofNat (nat_lit 46170)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
def block002_data_flat000 : CoefficientMerge.Poly := [(nat_lit 25, Int.negSucc (nat_lit 10259)), (nat_lit 106, Int.negSucc (nat_lit 20519)), (nat_lit 187, Int.negSucc (nat_lit 41039)), (nat_lit 196, Int.negSucc (nat_lit 20519)), (nat_lit 214, Int.ofNat (nat_lit 20520)), (nat_lit 223, Int.ofNat (nat_lit 30780)), (nat_lit 232, Int.ofNat (nat_lit 41040)), (nat_lit 233, Int.ofNat (nat_lit 46170))]
theorem block002_data_flat000_step : block002_data_flat000 = (CoefficientMerge.scale (2565 : Int) atom0160Coded) := by decide +kernel
theorem block002_data_flat000_original : block002_data_flat000 = (CoefficientMerge.scale (2565 : Int) atom0160Coded) := by
  rw [block002_data_flat000_step]
def block002_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 125279)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.ofNat (nat_lit 78300)), (nat_lit 17, Int.ofNat (nat_lit 140940))]
theorem block002_data_flat001_step : block002_data_flat001 = (CoefficientMerge.scale (7830 : Int) atom0161Coded) := by decide +kernel
theorem block002_data_flat001_original : block002_data_flat001 = (CoefficientMerge.scale (7830 : Int) atom0161Coded) := by
  rw [block002_data_flat001_step]
def block002_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 11, Int.negSucc (nat_lit 131759)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.ofNat (nat_lit 109800)), (nat_lit 26, Int.ofNat (nat_lit 197640))]
theorem block002_data_flat002_step : block002_data_flat002 = (CoefficientMerge.scale (10980 : Int) atom0162Coded) := by decide +kernel
theorem block002_data_flat002_original : block002_data_flat002 = (CoefficientMerge.scale (10980 : Int) atom0162Coded) := by
  rw [block002_data_flat002_step]
def block002_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 257039)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.ofNat (nat_lit 78300)), (nat_lit 17, Int.ofNat (nat_lit 140940)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.ofNat (nat_lit 109800)), (nat_lit 26, Int.ofNat (nat_lit 197640))]
theorem block002_data_flat003_step : block002_data_flat003 = (CoefficientMerge.fastMerge block002_data_flat001 block002_data_flat002) := by decide +kernel
theorem block002_data_flat003_original : block002_data_flat003 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded)) := by
  rw [block002_data_flat003_step, block002_data_flat001_original, block002_data_flat002_original]
def block002_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 257039)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.ofNat (nat_lit 78300)), (nat_lit 17, Int.ofNat (nat_lit 140940)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.ofNat (nat_lit 99540)), (nat_lit 26, Int.ofNat (nat_lit 197640)), (nat_lit 106, Int.negSucc (nat_lit 20519)), (nat_lit 187, Int.negSucc (nat_lit 41039)), (nat_lit 196, Int.negSucc (nat_lit 20519)), (nat_lit 214, Int.ofNat (nat_lit 20520)), (nat_lit 223, Int.ofNat (nat_lit 30780)), (nat_lit 232, Int.ofNat (nat_lit 41040)), (nat_lit 233, Int.ofNat (nat_lit 46170))]
theorem block002_data_flat004_step : block002_data_flat004 = (CoefficientMerge.fastMerge block002_data_flat000 block002_data_flat003) := by decide +kernel
theorem block002_data_flat004_original : block002_data_flat004 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2565 : Int) atom0160Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded))) := by
  rw [block002_data_flat004_step, block002_data_flat000_original, block002_data_flat003_original]
def block002_data_flat005 : CoefficientMerge.Poly := [(nat_lit 7, Int.negSucc (nat_lit 55439)), (nat_lit 16, Int.negSucc (nat_lit 83159)), (nat_lit 25, Int.negSucc (nat_lit 110879)), (nat_lit 34, Int.negSucc (nat_lit 97019)), (nat_lit 43, Int.negSucc (nat_lit 69299)), (nat_lit 52, Int.negSucc (nat_lit 13859)), (nat_lit 61, Int.ofNat (nat_lit 13860)), (nat_lit 70, Int.ofNat (nat_lit 69300)), (nat_lit 71, Int.ofNat (nat_lit 124740))]
theorem block002_data_flat005_step : block002_data_flat005 = (CoefficientMerge.scale (6930 : Int) atom0163Coded) := by decide +kernel
theorem block002_data_flat005_original : block002_data_flat005 = (CoefficientMerge.scale (6930 : Int) atom0163Coded) := by
  rw [block002_data_flat005_step]
def block002_data_flat006 : CoefficientMerge.Poly := [(nat_lit 17, Int.negSucc (nat_lit 1679)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780))]
theorem block002_data_flat006_step : block002_data_flat006 = (CoefficientMerge.scale (210 : Int) atom0164Coded) := by decide +kernel
theorem block002_data_flat006_original : block002_data_flat006 = (CoefficientMerge.scale (210 : Int) atom0164Coded) := by
  rw [block002_data_flat006_step]
def block002_data_flat007 : CoefficientMerge.Poly := [(nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
theorem block002_data_flat007_step : block002_data_flat007 = (CoefficientMerge.scale (9108 : Int) atom0165Coded) := by decide +kernel
theorem block002_data_flat007_original : block002_data_flat007 = (CoefficientMerge.scale (9108 : Int) atom0165Coded) := by
  rw [block002_data_flat007_step]
def block002_data_flat008 : CoefficientMerge.Poly := [(nat_lit 17, Int.negSucc (nat_lit 1679)), (nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
theorem block002_data_flat008_step : block002_data_flat008 = (CoefficientMerge.fastMerge block002_data_flat006 block002_data_flat007) := by decide +kernel
theorem block002_data_flat008_original : block002_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded)) := by
  rw [block002_data_flat008_step, block002_data_flat006_original, block002_data_flat007_original]
def block002_data_flat009 : CoefficientMerge.Poly := [(nat_lit 7, Int.negSucc (nat_lit 55439)), (nat_lit 16, Int.negSucc (nat_lit 83159)), (nat_lit 17, Int.negSucc (nat_lit 1679)), (nat_lit 25, Int.negSucc (nat_lit 110879)), (nat_lit 34, Int.negSucc (nat_lit 97019)), (nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 43, Int.negSucc (nat_lit 69299)), (nat_lit 52, Int.negSucc (nat_lit 13859)), (nat_lit 61, Int.ofNat (nat_lit 13860)), (nat_lit 70, Int.ofNat (nat_lit 69300)), (nat_lit 71, Int.ofNat (nat_lit 124740)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
theorem block002_data_flat009_step : block002_data_flat009 = (CoefficientMerge.fastMerge block002_data_flat005 block002_data_flat008) := by decide +kernel
theorem block002_data_flat009_original : block002_data_flat009 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6930 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded))) := by
  rw [block002_data_flat009_step, block002_data_flat005_original, block002_data_flat008_original]
def block002_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 7, Int.negSucc (nat_lit 55439)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 257039)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.negSucc (nat_lit 4859)), (nat_lit 17, Int.ofNat (nat_lit 139260)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.negSucc (nat_lit 11339)), (nat_lit 26, Int.ofNat (nat_lit 197640)), (nat_lit 34, Int.negSucc (nat_lit 97019)), (nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 43, Int.negSucc (nat_lit 69299)), (nat_lit 52, Int.negSucc (nat_lit 13859)), (nat_lit 61, Int.ofNat (nat_lit 13860)), (nat_lit 70, Int.ofNat (nat_lit 69300)), (nat_lit 71, Int.ofNat (nat_lit 124740)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 106, Int.negSucc (nat_lit 20519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780)), (nat_lit 187, Int.negSucc (nat_lit 41039)), (nat_lit 196, Int.negSucc (nat_lit 20519)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 214, Int.ofNat (nat_lit 20520)), (nat_lit 223, Int.ofNat (nat_lit 30780)), (nat_lit 232, Int.ofNat (nat_lit 41040)), (nat_lit 233, Int.ofNat (nat_lit 46170)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
theorem block002_data_flat010_step : block002_data_flat010 = (CoefficientMerge.fastMerge block002_data_flat004 block002_data_flat009) := by decide +kernel
theorem block002_data_flat010_original : block002_data_flat010 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2565 : Int) atom0160Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6930 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded)))) := by
  rw [block002_data_flat010_step, block002_data_flat004_original, block002_data_flat009_original]
def block002_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1, Int.negSucc (nat_lit 62639)), (nat_lit 2, Int.negSucc (nat_lit 87839)), (nat_lit 7, Int.negSucc (nat_lit 55439)), (nat_lit 10, Int.negSucc (nat_lit 93959)), (nat_lit 11, Int.negSucc (nat_lit 257039)), (nat_lit 12, Int.negSucc (nat_lit 109619)), (nat_lit 13, Int.negSucc (nat_lit 78299)), (nat_lit 14, Int.negSucc (nat_lit 15659)), (nat_lit 15, Int.ofNat (nat_lit 15660)), (nat_lit 16, Int.negSucc (nat_lit 4859)), (nat_lit 17, Int.ofNat (nat_lit 139260)), (nat_lit 20, Int.negSucc (nat_lit 175679)), (nat_lit 21, Int.negSucc (nat_lit 153719)), (nat_lit 22, Int.negSucc (nat_lit 109799)), (nat_lit 23, Int.negSucc (nat_lit 21959)), (nat_lit 24, Int.ofNat (nat_lit 21960)), (nat_lit 25, Int.negSucc (nat_lit 11339)), (nat_lit 26, Int.ofNat (nat_lit 197640)), (nat_lit 34, Int.negSucc (nat_lit 97019)), (nat_lit 40, Int.negSucc (nat_lit 72863)), (nat_lit 43, Int.negSucc (nat_lit 69299)), (nat_lit 52, Int.negSucc (nat_lit 13859)), (nat_lit 61, Int.ofNat (nat_lit 13860)), (nat_lit 70, Int.ofNat (nat_lit 69300)), (nat_lit 71, Int.ofNat (nat_lit 124740)), (nat_lit 98, Int.negSucc (nat_lit 2519)), (nat_lit 106, Int.negSucc (nat_lit 20519)), (nat_lit 107, Int.negSucc (nat_lit 3359)), (nat_lit 116, Int.negSucc (nat_lit 2939)), (nat_lit 121, Int.negSucc (nat_lit 109295)), (nat_lit 125, Int.negSucc (nat_lit 2099)), (nat_lit 134, Int.negSucc (nat_lit 419)), (nat_lit 143, Int.ofNat (nat_lit 420)), (nat_lit 152, Int.ofNat (nat_lit 2100)), (nat_lit 161, Int.ofNat (nat_lit 3780)), (nat_lit 187, Int.negSucc (nat_lit 41039)), (nat_lit 196, Int.negSucc (nat_lit 20519)), (nat_lit 202, Int.negSucc (nat_lit 145727)), (nat_lit 214, Int.ofNat (nat_lit 20520)), (nat_lit 223, Int.ofNat (nat_lit 30780)), (nat_lit 232, Int.ofNat (nat_lit 41040)), (nat_lit 233, Int.ofNat (nat_lit 46170)), (nat_lit 283, Int.negSucc (nat_lit 127511)), (nat_lit 364, Int.negSucc (nat_lit 91079)), (nat_lit 365, Int.negSucc (nat_lit 18215)), (nat_lit 366, Int.ofNat (nat_lit 18216)), (nat_lit 367, Int.ofNat (nat_lit 91080)), (nat_lit 368, Int.ofNat (nat_lit 163944))]
theorem block002_data_flat011_step : block002_data_flat011 = (CoefficientMerge.trim block002_data_flat010) := by decide +kernel
theorem block002_data_flat011_original : block002_data_flat011 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2565 : Int) atom0160Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6930 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded))))) := by
  rw [block002_data_flat011_step, block002_data_flat010_original]
theorem block002_data : block002 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2565 : Int) atom0160Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6930 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded)))) := by
  have h : block002 = block002_data_flat011 := by decide +kernel
  exact h.trans block002_data_flat011_original
theorem block002_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) block002 := by
  rw [block002_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (atom0160Coded_nonneg g hg hA hB) (add_nonneg (atom0161Coded_nonneg g hg hA hB) (atom0162Coded_nonneg g hg hA hB))) (add_nonneg (atom0163Coded_nonneg g hg hA hB) (add_nonneg (atom0164Coded_nonneg g hg hA hB) (atom0165Coded_nonneg g hg hA hB))))

end APPT.Finite9
