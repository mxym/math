import GaussianRegularStationarity

/-! The entire actual price objective, not just its infimum, depends only
on the score Gram matrix. In particular every regular Gram realization has
zero balancing prices, including embeddings into arbitrary dimensions. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e k : ℕ} [NeZero k]

theorem priceObjective_eq_of_gram_eq (v : Fin k → Space d) (u : Fin k → Space e)
    (hg : scoreGram v = scoreGram u) (p b : Fin k → ℝ) :
    priceObjective v p b = priceObjective u p b := by
  simp only [priceObjective,expectedScore_eq_of_gram_eq v u hg b]

theorem canonicalPrices_scaled_regular_gram (hk : 2 ≤ k)
    (v : Fin k → Space d) (hv : Function.Injective v) (c : ℝ) (hc : 0 ≤ c)
    (hg : scoreGram v = c^2 • regularCovariance k) : canonicalPrices v = 0 := by
  have hgram : scoreGram v = scoreGram (c • regularRows k) := by
    rw [scoreGram_smul]
    exact hg
  have hvalue : equalMassValue v = c*simplexConstant k := by
    rw [equalMassValue_eq_of_gram_eq v _ hgram,equalMassValue_smul _ c hc,
      ← covarianceValue_scoreGram,← regularCovariance,covarianceValue_regular]
  have hprice : priceObjective v (uniformMass k) 0 = c*simplexConstant k := by
    rw [priceObjective_eq_of_gram_eq v _ hgram]
    have he := priceObjective_smul (regularRows k) (uniformMass k) 0 c hc
    simp only [smul_zero] at he
    rw [he,← canonicalPrices_regular hk,canonicalPrices_value,
      ← covarianceValue_scoreGram,← regularCovariance,covarianceValue_regular]
  apply Eq.symm
  apply canonicalPrices_unique v hv 0 _ rfl
  intro b
  rw [hprice,← hvalue]
  exact balancedValue_le_objective v (uniformMass k) b uniformMass_pos sum_uniformMass

end GaussianMeasureBridge
