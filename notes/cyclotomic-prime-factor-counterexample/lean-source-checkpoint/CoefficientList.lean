import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace CyclotomicCounterexample
open Polynomial

/-- Horner polynomial of an ascending integer coefficient list. -/
noncomputable def ofCoeffs : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: as => C a + X * ofCoeffs as

theorem coeff_ofCoeffs (as : List ℤ) (k : ℕ) :
    (ofCoeffs as).coeff k = as[k]?.getD 0 := by
  induction as generalizing k with
  | nil => simp [ofCoeffs]
  | cons a as ih =>
    cases k with
    | zero => simp [ofCoeffs]
    | succ k =>
      simp only [ofCoeffs, coeff_add, coeff_C, coeff_X_mul, Nat.succ_ne_zero, ite_false, zero_add]
      simpa using ih k

end CyclotomicCounterexample
