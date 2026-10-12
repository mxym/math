import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace HydrologyIdentifiability

open scoped BigOperators

noncomputable section

/-- The finite moment sequence of a weighted collection of decay rates. -/
def finiteMoment {k : ℕ} (w l : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i, w i * l i ^ j

/-- Any polynomial that annihilates every rate induces an exact linear
recurrence on all moments, for every starting index. This is the finite-mode
model-order identity behind the explicit two- and three-mode certificates. -/
theorem annihilating_recurrence {k d : ℕ} (w l : Fin k → ℝ)
    (c : Fin (d + 1) → ℝ)
    (hroot : ∀ i, ∑ r, c r * l i ^ (r : ℕ) = 0) (j : ℕ) :
    ∑ r, c r * finiteMoment w l (j + (r : ℕ)) = 0 := by
  classical
  simp only [finiteMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  have hfactor : (∑ x, c x * (w i * l i ^ (j + (x : ℕ)))) =
      w i * l i ^ j * (∑ x, c x * l i ^ (x : ℕ)) := by
    simp_rw [pow_add]
    calc
      (∑ x, c x * (w i * (l i ^ j * l i ^ (x : ℕ)))) =
          ∑ x, (w i * l i ^ j) * (c x * l i ^ (x : ℕ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = w i * l i ^ j * (∑ x, c x * l i ^ (x : ℕ)) := by
            rw [Finset.mul_sum]
  rw [hfactor, hroot i]
  ring

end
end HydrologyIdentifiability
