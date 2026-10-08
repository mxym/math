import BapatLaplace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped Topology ENNReal

namespace BapatRealExistence

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Normalized angular Haar measure on the actual Euclidean unit sphere. -/
def normalizedSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

variable (μ : Measure E) [IsAddHaarMeasure μ]

instance normalizedSphere_isProbability : IsProbabilityMeasure (normalizedSphere μ) where
  measure_univ := by
    have h0 : μ.toSphere univ ≠ 0 := by
      intro he
      apply μ.toSphere_ne_zero
      exact measure_univ_eq_zero.mp he
    simp only [normalizedSphere, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)

instance normalizedSphere_isOpenPos : IsOpenPosMeasure (normalizedSphere μ) :=
  isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

theorem sphere_power_integral_pos (f : sphere (0 : E) 1 → ℝ)
    (hf : Continuous f) (hnf : ∀ x, 0 ≤ f x) (x₀ : sphere (0 : E) 1)
    (hpos : 0 < f x₀) (n : ℕ) :
    0 < ∫ x, (f x)^n ∂normalizedSphere μ := by
  exact (hf.pow n).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun x => pow_nonneg (hnf x) n)
    (pow_ne_zero n hpos.ne')

/-- The concentration theorem now has a concrete finite full-support sphere
probability measure; none of these measure properties is an extra hypothesis. -/
theorem sphere_even_power_integral_ratio
    (f g : sphere (0 : E) 1 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hnf : ∀ x, 0 ≤ f x) (x₀ : sphere (0 : E) 1) (hpos : 0 < f x₀)
    (hmax : ∀ x, f x ≤ f x₀) (hcommon : ∀ x, f x = f x₀ → g x = g x₀) :
    Tendsto (fun L : ℕ => (∫ x, f x ^ (2*L-2) * g x ∂normalizedSphere μ) /
      ∫ x, f x ^ (2*L) ∂normalizedSphere μ) atTop (𝓝 (g x₀ / (f x₀)^2)) := by
  exact tendsto_even_power_integral_ratio f g hf hg hnf x₀ hpos hmax hcommon

end
end BapatRealExistence
