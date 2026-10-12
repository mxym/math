import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Exclusion of prime cyclotomic factors

Distinct cyclotomic polynomials over `ℚ` are relatively prime. Consequently a
positive-index cyclotomic polynomial whose index differs from `4`, `9`, `25`,
and `30` cannot divide any power of their product. In particular, no prime-index
cyclotomic polynomial divides the sixth power, over either `ℚ` or `ℤ`.
-/

namespace CyclotomicCounterexample

open Polynomial

/-- An absent positive cyclotomic index stays absent after any nonnegative power. -/
theorem cyclotomic_not_dvd_product_pow_rat {n : ℕ} (hn : 0 < n)
    (h4 : n ≠ 4) (h9 : n ≠ 9) (h25 : n ≠ 25) (h30 : n ≠ 30) (k : ℕ) :
    ¬ cyclotomic n ℚ ∣
      (cyclotomic 4 ℚ * cyclotomic 9 ℚ * cyclotomic 25 ℚ * cyclotomic 30 ℚ) ^ k := by
  have hc : IsCoprime (cyclotomic n ℚ)
      (cyclotomic 4 ℚ * cyclotomic 9 ℚ * cyclotomic 25 ℚ * cyclotomic 30 ℚ) :=
    (((cyclotomic.isCoprime_rat h4).mul_right
      (cyclotomic.isCoprime_rat h9)).mul_right
      (cyclotomic.isCoprime_rat h25)).mul_right (cyclotomic.isCoprime_rat h30)
  intro hd
  exact (cyclotomic.irreducible_rat hn).not_isUnit ((hc.pow_right).isUnit_of_dvd hd)

/-- No prime-index cyclotomic polynomial divides the rational sixth power. -/
theorem prime_cyclotomic_not_dvd_rat (p : ℕ) (hp : Nat.Prime p) :
    ¬ cyclotomic p ℚ ∣
      (cyclotomic 4 ℚ * cyclotomic 9 ℚ * cyclotomic 25 ℚ * cyclotomic 30 ℚ) ^ 6 := by
  apply cyclotomic_not_dvd_product_pow_rat hp.pos
  all_goals intro h; subst p; norm_num at hp

/-- No prime-index cyclotomic polynomial divides the integer sixth power. -/
theorem prime_cyclotomic_not_dvd_int (p : ℕ) (hp : Nat.Prime p) :
    ¬ cyclotomic p ℤ ∣
      (cyclotomic 4 ℤ * cyclotomic 9 ℤ * cyclotomic 25 ℤ * cyclotomic 30 ℤ) ^ 6 := by
  intro hd
  apply prime_cyclotomic_not_dvd_rat p hp
  have hm := Polynomial.map_dvd (Int.castRingHom ℚ) hd
  simpa only [Polynomial.map_pow, Polynomial.map_mul, map_cyclotomic_int] using hm

end CyclotomicCounterexample
