import Expansion
import BasicProperties

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace CyclotomicCounterexample
open Polynomial

/-- Positive weights in the centered q-integer expansion, in ascending shift order. -/
def centeredWeights : List ℤ :=
  [1, 5, 15, 35, 64, 96, 126, 150,
   180, 238, 326, 426, 501, 531, 567, 701,
   991, 1371, 1692, 1866, 1980, 2326, 3071, 4023,
   4806, 5124, 5250, 5856, 7269, 9147, 10585, 11189,
   11655, 13079, 15982, 19290, 21585, 22779, 24183, 27587,
   32545, 36825, 39095, 40213, 43527, 50235, 57570, 62100,
   62948, 64882, 72555, 84635, 95020, 97758, 96567, 100479,
   113595, 130975, 140138, 138138, 135060, 142464, 162645, 180663,
   184173, 177591, 176555, 194149, 218922, 230692, 223826, 212586,
   221560, 248612, 269481, 265241, 241396, 232836, 254723, 286675,
   295956, 268346, 238156, 241074, 275394, 304410, 288381, 244691,
   218995, 235689, 273250, 275390, 232581, 184211, 174619, 208125,
   227485, 197435, 138246, 102744, 124275, 158475, 150360, 91356,
   28794, 23500, 59600, 78150, 38406]

theorem centeredWeights_length : centeredWeights.length = 109 := by decide

theorem centeredWeights_zero : centeredWeights[0]?.getD 0 = 1 := by decide

theorem centeredWeights_positive :
    ∀ j : Fin 109, 0 < centeredWeights[j.val]?.getD 0 := by decide

/-- A q-integer is the polynomial 1 + X + ... + X^(m-1). -/
noncomputable def qInteger (m : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range m, X^i

/-- Every q-integer summand here has the same center, namely degree 108. -/
noncomputable def centeredExpansion : Polynomial ℤ :=
  ∑ j ∈ Finset.range 109,
    C (centeredWeights[j]?.getD 0) * X^j * qInteger (217 - 2*j)

theorem qInteger_coeff (m k : ℕ) :
    (qInteger m).coeff k = if k < m then 1 else 0 := by
  simp [qInteger, finsetSum_coeff, coeff_X_pow, Finset.mem_range]

theorem centeredTerm_coeff (w : ℤ) (j m k : ℕ) :
    (C w * X^j * qInteger m).coeff k =
      if j ≤ k ∧ k-j < m then w else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [qInteger_coeff]
  split_ifs <;> simp_all

/-- A computable integer expression for each coefficient of the centered sum. -/
def centeredCoefficient (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range 109,
    if j ≤ k ∧ k-j < 217-2*j then centeredWeights[j]?.getD 0 else 0

theorem centeredExpansion_coeff (k : ℕ) :
    centeredExpansion.coeff k = centeredCoefficient k := by
  simp only [centeredExpansion, finsetSum_coeff, centeredTerm_coeff, centeredCoefficient]

/-- Finite arithmetic certificate, proved by the kernel's ordinary decision procedure. -/
theorem centered_coefficients_match :
    ∀ k : Fin 217, centeredCoefficient k.val = coefficients[k.val]?.getD 0 := by
  decide

theorem centeredCoefficient_tail (k : ℕ) (hk : 217 ≤ k) : centeredCoefficient k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < 109 := Finset.mem_range.mp hj
  have hbad : ¬(j ≤ k ∧ k-j < 217-2*j) := by omega
  simp only [ite_eq_right hbad]

theorem coefficient_polynomial_eq_centeredExpansion :
    ofCoeffs coefficients = centeredExpansion := by
  ext k
  rw [coeff_ofCoeffs, centeredExpansion_coeff]
  by_cases hk : k < 217
  · exact (centered_coefficients_match ⟨k, hk⟩).symm
  · rw [centeredCoefficient_tail k (by omega)]
    have hlen : coefficients.length = 217 := by decide
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem product_eq_centeredExpansion :
    (cyclotomic 4 ℤ * cyclotomic 9 ℤ * cyclotomic 25 ℤ * cyclotomic 30 ℤ)^6 =
      centeredExpansion := by
  rw [product_eq_coefficient_polynomial, coefficient_polynomial_eq_centeredExpansion]

/-- The literal centered q-integer expansion of the genuine cyclotomic product. -/
theorem F_centered_qInteger_expansion :
    F = ∑ j ∈ Finset.range 109,
      C (centeredWeights[j]?.getD 0) * X^j *
        (∑ k ∈ Finset.range (217-2*j), (X : Polynomial ℤ)^k) := by
  exact product_eq_centeredExpansion

/-- The centered certificate includes positivity of every weight and initial weight one. -/
theorem F_centered_certificate :
    centeredWeights.length = 109 ∧
    centeredWeights[0]?.getD 0 = 1 ∧
    (∀ j : Fin 109, 0 < centeredWeights[j.val]?.getD 0) ∧
    F = ∑ j ∈ Finset.range 109,
      C (centeredWeights[j]?.getD 0) * X^j *
        (∑ k ∈ Finset.range (217-2*j), (X : Polynomial ℤ)^k) := by
  exact ⟨centeredWeights_length, centeredWeights_zero,
    centeredWeights_positive, F_centered_qInteger_expansion⟩

/-- Numerator of the q-integer presentation before taking the sixth power. -/
noncomputable def qIntegerNumerator : Polynomial ℤ :=
  qInteger 4 * qInteger 9 * qInteger 25 * qInteger 30

/-- Denominator of the q-integer presentation before taking the sixth power. -/
noncomputable def qIntegerDenominator : Polynomial ℤ :=
  qInteger 1 * qInteger 6 * qInteger 10 * qInteger 15

/-- Polynomial identity certifying the q-integer quotient without using division. -/
theorem qInteger_base_identity :
    qIntegerNumerator =
      (cyclotomic 4 ℤ * cyclotomic 9 ℤ * cyclotomic 25 ℤ * cyclotomic 30 ℤ) *
        qIntegerDenominator := by
  rw [cyclotomic_four_int, cyclotomic_nine_int, cyclotomic_twenty_five_int,
    cyclotomic_thirty_int]
  simp only [qIntegerNumerator, qIntegerDenominator, qInteger, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

theorem qInteger_eval_one (m : ℕ) : (qInteger m).eval 1 = (m : ℤ) := by
  simp [qInteger]

theorem qIntegerDenominator_eval_one : qIntegerDenominator.eval 1 = 900 := by
  simp [qIntegerDenominator, qInteger_eval_one]

theorem qIntegerDenominator_ne_zero : qIntegerDenominator ≠ 0 := by
  intro h
  have he := qIntegerDenominator_eval_one
  rw [h] at he
  norm_num at he

/-- The original basic-CGF quotient identity, fully cleared of its nonzero denominator. -/
theorem F_qInteger_quotient_certificate :
    qIntegerNumerator^6 = F * qIntegerDenominator^6 ∧ qIntegerDenominator^6 ≠ 0 := by
  constructor
  · rw [qInteger_base_identity, mul_pow]
    rfl
  · exact pow_ne_zero _ qIntegerDenominator_ne_zero

#print axioms F_qInteger_quotient_certificate
#print axioms F_centered_certificate
#print axioms centeredWeights_positive

end CyclotomicCounterexample
