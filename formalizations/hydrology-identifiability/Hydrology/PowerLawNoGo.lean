import Hydrology.FiniteBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace HydrologyIdentifiability

open scoped BigOperators

noncomputable section

/-- A positive sequence whose consecutive ratio grows linearly in the index
cannot have a uniform finite upper ratio bound. This is the exact discrete
core of the power-law recession obstruction. -/
theorem no_bounded_ratio_linear_growth
    (M : ℕ → ℝ) (α τ L : ℝ)
    (hα : 0 < α) (hτ : 0 < τ) (hM0 : 0 < M 0)
    (hrec : ∀ j : ℕ,
      M (j + 1) = ((α + (j : ℝ)) / τ) * M j)
    (hbound : ∀ j : ℕ, M (j + 1) ≤ L * M j) :
    False := by
  have hpos : ∀ j : ℕ, 0 < M j := by
    intro j
    induction j with
    | zero => exact hM0
    | succ j ih =>
        rw [hrec j]
        have hfactor : 0 < (α + (j : ℝ)) / τ := by positivity
        positivity
  obtain ⟨j, hj⟩ : ∃ j : ℕ, τ * L - α < (j : ℝ) :=
    exists_nat_gt (τ * L - α)
  have hnum : τ * L < α + (j : ℝ) := by linarith
  have hratio : L < (α + (j : ℝ)) / τ := by
    apply (lt_div_iff₀ hτ).2
    linarith
  have hineq := hbound j
  rw [hrec j] at hineq
  have hp := hpos j
  nlinarith

/-- A finite positive-rate exponential spectrum cannot satisfy the exact
shifted-power-law moment ratio for every derivative order. The finite-spectrum
growth bound is kernel-checked; no integral or numerical approximation enters
this theorem. -/
theorem finite_spectrum_powerlaw_ratio_impossible
    {k : ℕ} (w l : Fin k → ℝ) (L α τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hl : ∀ i, 0 ≤ l i)
    (hL : ∀ i, l i ≤ L) (hα : 0 < α) (hτ : 0 < τ)
    (hM0 : 0 < finiteMoment w l 0)
    (hpower : ∀ j : ℕ,
      finiteMoment w l (j + 1) =
        ((α + (j : ℝ)) / τ) * finiteMoment w l j) :
    False := by
  apply no_bounded_ratio_linear_growth (finiteMoment w l) α τ L hα hτ hM0 hpower
  intro j
  exact finiteMoment_rate_bound w l L hw hl hL j

end
end HydrologyIdentifiability
