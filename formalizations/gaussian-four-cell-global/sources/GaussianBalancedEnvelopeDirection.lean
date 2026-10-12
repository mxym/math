import GaussianScoreDerivative

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma affine_weighted_prices (p b q : Fin k → ℝ) (t : ℝ) :
    (∑ i, p i * affinePrices b q t i) =
      (∑ i, p i * b i) + t * ∑ i, p i * q i := by
  simp only [affinePrices, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- At actual balancing prices, every first-order price direction cancels.
This is the envelope differential of the score-price objective at its
minimizer. The statement does not assume that affine price paths stay optimal. -/
theorem priceObjective_directional_derivative_at_balancing
    (v h : Fin k → Space d) (p b q : Fin k → ℝ) (hv : Function.Injective v)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = p i) :
    HasDerivAt (fun t => priceObjective (affineScores v h t) p (affinePrices b q t))
      (∑ i, ⟪h i, (winningPartition v b hv).moment i⟫) 0 := by
  have hd := expectedScore_directional_derivative v h b q hv
  have hp : HasDerivAt (fun t : ℝ => ∑ i, p i * affinePrices b q t i)
      (∑ i, p i * q i) 0 := by
    simp_rw [affine_weighted_prices]
    convert (hasDerivAt_const 0 (∑ i, p i * b i)).add
      ((hasDerivAt_id 0).mul_const (∑ i, p i * q i)) using 1
    · rfl
    · simp
  have hh := hd.add hp
  simp_rw [winningPartition_mass, hb] at hh
  convert hh using 1
  · rfl
  · ring

end GaussianMeasureBridge
