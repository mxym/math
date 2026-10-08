import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Explicit formulas for actual integer cyclotomic polynomials

All four identities below concern Mathlib's `Polynomial.cyclotomic`.
The prime-power identities follow from its geometric-sum theorem, and the
thirtieth identity follows from cyclotomic expansion and cancellation.
-/

namespace CyclotomicCounterexample

open Polynomial

/-- The fourth cyclotomic polynomial over the integers. -/
theorem cyclotomic_four_int :
    cyclotomic 4 ℤ = 1 + (X : Polynomial ℤ) ^ 2 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) Nat.prime_two
  simpa [Finset.sum_range_succ] using h

/-- The ninth cyclotomic polynomial over the integers. -/
theorem cyclotomic_nine_int :
    cyclotomic 9 ℤ = 1 + (X : Polynomial ℤ) ^ 3 + X ^ 6 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) Nat.prime_three
  simpa [Finset.sum_range_succ, ← pow_mul] using h

/-- The twenty-fifth cyclotomic polynomial over the integers. -/
theorem cyclotomic_twenty_five_int :
    cyclotomic 25 ℤ = 1 + (X : Polynomial ℤ) ^ 5 + X ^ 10 + X ^ 15 + X ^ 20 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1)
    (by norm_num : Nat.Prime 5)
  simpa [Finset.sum_range_succ, ← pow_mul] using h

/-- The thirtieth cyclotomic polynomial over the integers. -/
theorem cyclotomic_thirty_int :
    cyclotomic 30 ℤ =
      1 + (X : Polynomial ℤ) - X ^ 3 - X ^ 4 - X ^ 5 + X ^ 7 + X ^ 8 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 6 ℤ)
  rw [show 30 = 6 * 5 by rfl,
    ← cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 5) (by norm_num)]
  simp
  ring

end CyclotomicCounterexample
