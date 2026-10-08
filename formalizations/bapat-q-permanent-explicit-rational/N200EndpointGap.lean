import BapatN200Trace
import BapatN200Matrix
import BapatExactStateBridge
import DefinitionBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

/-- Integrality strengthens the certified strict gap to a unit gap. -/
theorem integer_norm_gap_at_least_one :
    (1 : ℤ) ≤ wedgeNorm - 19900 * permanentNorm := by
  have h := norm_gap_positive
  omega

theorem permanentNorm_eq_fischer : (permanentNorm : ℝ) =
    BapatFischer.fischerNormSq 200 (BapatFischer.twoColorProduct a b) := by
  unfold permanentNorm
  rw [← state_eq_200]
  exact fischerInt_state_f (vectorAt vectors) 200

theorem wedgeNorm_eq_fischer : (wedgeNorm : ℝ) =
    BapatFischer.fischerNormSq 198 (wedgePolynomial a b) := by
  unfold wedgeNorm
  rw [← state_eq_200]
  exact fischerInt_state_s (vectorAt vectors) 200

/-- No negative-input premise: the actual matrix is the certified 200-row Gram. -/
theorem matrix_endpoint_unit_gap : (Bapat.endpointDerivative matrix).re ≤ -(1 / 2 : ℝ) := by
  have hgap : (1 : ℝ) ≤ (wedgeNorm : ℝ) - 19900 * (permanentNorm : ℝ) := by
    exact_mod_cast integer_norm_gap_at_least_one
  have hid := realQPolynomial_derivative_fischer a b
  change 2 * (realQPolynomial matrix).derivative.eval 1 = _ at hid
  have hn : (Nat.choose 200 2 : ℝ) = 19900 := by norm_num [Nat.choose_two_right]
  rw [hn, ← permanentNorm_eq_fischer, ← wedgeNorm_eq_fischer] at hid
  rw [endpointDerivative_eq]
  linarith

end BapatExplicit
