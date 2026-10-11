import Hydrology.Generic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace HydrologyIdentifiability

open scoped BigOperators

noncomputable section

/-- Nonnegative weights and rates give nonnegative finite moments. -/
theorem finiteMoment_nonneg {k : ℕ} (w l : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hl : ∀ i, 0 ≤ l i) (j : ℕ) :
    0 ≤ finiteMoment w l j := by
  classical
  unfold finiteMoment
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (pow_nonneg (hl i) j)

/-- If every rate is at most `L`, consecutive finite moments obey the exact
ratio bound `M_(j+1) ≤ L M_j`. This is the finite-spectrum growth invariant
used to distinguish finite exponential mixtures from power-law derivatives. -/
theorem finiteMoment_rate_bound {k : ℕ} (w l : Fin k → ℝ) (L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hl : ∀ i, 0 ≤ l i)
    (hL : ∀ i, l i ≤ L) (j : ℕ) :
    finiteMoment w l (j + 1) ≤ L * finiteMoment w l j := by
  classical
  unfold finiteMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hp : 0 ≤ l i ^ j := pow_nonneg (hl i) j
  have hstep : l i ^ j * l i ≤ l i ^ j * L :=
    mul_le_mul_of_nonneg_left (hL i) hp
  have hw' := mul_le_mul_of_nonneg_left hstep (hw i)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hw'

end
end HydrologyIdentifiability
