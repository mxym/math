import Expansion

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace CyclotomicCounterexample

def a (k : ℕ) : ℤ := coefficients[k]?.getD 0

theorem coefficients_length : coefficients.length = 217 := by decide

theorem data_positive : ∀ k : Fin 217, 0 < a k := by decide

theorem data_increase : ∀ k : Fin 108, 5 ≤ a (k + 1) - a k := by decide

theorem data_decrease : ∀ k : Fin 108, 5 ≤ a (108 + k) - a (109 + k) := by decide

theorem data_palindrome : ∀ k : Fin 217, a k = a (216 - k) := by decide

theorem data_peak : a 108 = 11434392 := by decide

theorem data_unique_peak : ∀ k : Fin 217, (k : ℕ) ≠ 108 → a k < a 108 := by decide

theorem data_first_difference : a 1 - a 0 = 5 := by decide

theorem data_zero_tail (k : ℕ) (hk : 216 < k) : a k = 0 := by
  unfold a
  rw [List.getElem?_eq_none_iff.mpr]
  · rfl
  · rw [coefficients_length]
    omega

end CyclotomicCounterexample
