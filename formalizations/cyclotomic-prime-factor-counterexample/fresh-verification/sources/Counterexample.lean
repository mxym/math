import BasicProperties
import DataProperties
import PrimeExclusion

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace CyclotomicCounterexample

/-- Exact coefficient identity linking the finite certificate to every natural index. -/
theorem F_coeff (k : ℕ) : F.coeff k = a k := by
  rw [F, product_eq_coefficient_polynomial, coeff_ofCoeffs]
  rfl

theorem F_coeff_positive (k : ℕ) (hk : k ≤ 216) : 0 < F.coeff k := by
  rw [F_coeff]
  exact data_positive ⟨k, by omega⟩

theorem F_coeff_zero_tail (k : ℕ) (hk : 216 < k) : F.coeff k = 0 := by
  rw [F_coeff]
  exact data_zero_tail k hk

theorem F_nonnegative : NonnegativeCoeffs F := by
  intro k
  by_cases hk : k ≤ 216
  · exact (F_coeff_positive k hk).le
  · rw [F_coeff_zero_tail k (by omega)]

theorem F_strict_increase (k : ℕ) (hk : k < 108) :
    F.coeff k < F.coeff (k + 1) := by
  rw [F_coeff, F_coeff]
  have h := data_increase ⟨k, hk⟩
  change 5 ≤ a (k + 1) - a k at h
  omega

theorem F_increase_margin (k : ℕ) (hk : k < 108) :
    5 ≤ F.coeff (k + 1) - F.coeff k := by
  simpa only [F_coeff] using data_increase ⟨k, hk⟩

theorem F_strict_decrease (k : ℕ) (hl : 108 ≤ k) (hu : k < 216) :
    F.coeff (k + 1) < F.coeff k := by
  rw [F_coeff, F_coeff]
  have h := data_decrease ⟨k - 108, by omega⟩
  change 5 ≤ a (108 + (k - 108)) - a (109 + (k - 108)) at h
  have h₁ : 108 + (k - 108) = k := by omega
  have h₂ : 109 + (k - 108) = k + 1 := by omega
  rw [h₁, h₂] at h
  omega

theorem F_palindrome (k : ℕ) (hk : k ≤ 216) : F.coeff k = F.coeff (216-k) := by
  simpa only [F_coeff] using data_palindrome ⟨k, by omega⟩

theorem F_unique_peak (k : ℕ) (hk : k ≠ 108) : F.coeff k < F.coeff 108 := by
  by_cases h : k ≤ 216
  · simpa only [F_coeff] using data_unique_peak ⟨k, by omega⟩ hk
  · rw [F_coeff_zero_tail k (by omega), F_coeff, data_peak]
    norm_num

theorem F_peak_value : F.coeff 108 = 11434392 := by rw [F_coeff, data_peak]

theorem F_minimum_increase : F.coeff 1 - F.coeff 0 = 5 ∧
    ∀ k : ℕ, k < 108 → 5 ≤ F.coeff (k + 1) - F.coeff k := by
  exact ⟨by simpa only [F_coeff] using data_first_difference, F_increase_margin⟩

theorem F_unimodal : UnimodalCoeffs F := by
  refine ⟨108, ?_, ?_⟩
  · have hmono : StrictMono (fun k : Fin 109 => F.coeff k) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro k
      exact F_strict_increase k k.isLt
    intro i j hij hj
    exact hmono.monotone (show (⟨i, by omega⟩ : Fin 109) ≤ ⟨j, by omega⟩ from hij)
  · have hanti : AntitoneOn (fun k : ℕ => F.coeff k) { k | 108 ≤ k } := by
      apply antitoneOn_nat_Ici_of_succ_le
      intro k hk
      by_cases hu : k < 216
      · exact (F_strict_decrease k hk hu).le
      · rw [F_coeff_zero_tail (k+1) (by omega)]
        exact F_nonnegative k
    intro i j hi hij
    exact hanti hi (show 108 ≤ j from le_trans hi hij) hij

theorem F_basic : IsBasicCGF F := F_isBasicCGF_of_nonnegative F_nonnegative

theorem F_no_prime_cyclotomic (p : ℕ) (hp : Nat.Prime p) :
    ¬ Polynomial.cyclotomic p ℤ ∣ F := by
  simpa only [F] using prime_cyclotomic_not_dvd_int p hp

/-- Billey--Swanson Conjecture 48 in its published basic, unimodal form. -/
def Conjecture48 : Prop :=
  ∀ f : Polynomial ℤ, IsBasicCGF f → UnimodalCoeffs f → f ≠ 1 →
    ∃ p : ℕ, Nat.Prime p ∧ Polynomial.cyclotomic p ℤ ∣ f

/-- Complete explicit counterexample, with no unproved certificate assumptions. -/
theorem explicit_counterexample :
    IsBasicCGF F ∧ UnimodalCoeffs F ∧ F ≠ 1 ∧ F.Monic ∧
    F.degree = 216 ∧ F.natDegree = 216 ∧ F.coeff 0 = 1 ∧
    (∀ k : ℕ, 0 ≤ F.coeff k) ∧
    (∀ k : ℕ, k ≤ 216 → 0 < F.coeff k) ∧
    (∀ k : ℕ, k < 108 → F.coeff k < F.coeff (k+1)) ∧
    (∀ k : ℕ, 108 ≤ k → k < 216 → F.coeff (k+1) < F.coeff k) ∧
    (∀ k : ℕ, k ≠ 108 → F.coeff k < F.coeff 108) ∧
    (∀ p : ℕ, Nat.Prime p → ¬ Polynomial.cyclotomic p ℤ ∣ F) := by
  exact ⟨F_basic, F_unimodal, F_ne_one, F_monic, F_degree, F_natDegree, F_coeff_zero,
    F_nonnegative, F_coeff_positive, F_strict_increase, F_strict_decrease,
    F_unique_peak, F_no_prime_cyclotomic⟩

theorem conjecture48_false : ¬ Conjecture48 := by
  intro h
  obtain ⟨p, hp, hd⟩ := h F F_basic F_unimodal F_ne_one
  exact F_no_prime_cyclotomic p hp hd

end CyclotomicCounterexample
