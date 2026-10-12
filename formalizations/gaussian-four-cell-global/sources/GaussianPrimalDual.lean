import GaussianUniquePrices

/-! Actual Gaussian finite-label primal-dual attainment under explicit distinct
score vectors. This is a dependency, not the geometric Gaussian sharp theorem. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def partitionValue (v : Fin k → Space d) (F : FractionalPartition d k) : ℝ :=
  ∑ i, ⟪v i, F.moment i⟫

/-- Actual Bochner primal optimum equals an attained finite Gaussian price dual.
The winning partition has the prescribed masses, and every measurable
fractional competitor with those masses has no larger objective. -/
theorem actual_gaussian_primal_dual (v : Fin k → Space d) (p : Fin k → ℝ)
    (hv : Function.Injective v) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ b : Fin k → ℝ, ∃ F : FractionalPartition d k,
      (∀ i, F.mass i = p i) ∧
      partitionValue v F = priceObjective v p b ∧
      (∀ G : FractionalPartition d k, (∀ i, G.mass i = p i) →
        partitionValue v G ≤ partitionValue v F) ∧
      (∀ c, priceObjective v p b ≤ priceObjective v p c) ∧
      (∀ c, (∀ i, (gaussian d).real (winningCell v c i) = p i) →
        ∃ a : ℝ, ∀ i, c i = b i + a) := by
  obtain ⟨b, hb⟩ := exists_balancing_prices v p hv hp hs
  let F := winningPartition v b hv
  have hm : ∀ i, F.mass i = p i := fun i => by
    rw [winningPartition_mass]
    exact hb i
  have hvF : partitionValue v F = priceObjective v p b := by
    unfold partitionValue
    rw [winningPartition_dual_attainment]
    simp_rw [winningPartition_mass, hb]
    rfl
  refine ⟨b, F, hm, hvF, ?_, balanced_price_is_minimizer v p b hv hb, ?_⟩
  · intro G hG
    have hd := G.price_dual v b
    simp_rw [hG] at hd
    rw [hvF]
    exact hd
  · intro c hc
    exact balancing_prices_unique_mod_const v p b c hv hp hb hc

end GaussianMeasureBridge
