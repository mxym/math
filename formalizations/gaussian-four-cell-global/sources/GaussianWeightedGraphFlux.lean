import GaussianWeightedHalflineFlux
import GaussianGraphMassDerivative

/-! Weighted vertical Gaussian divergence on a genuine epigraph, by Fubini
and compact-test half-line integration by parts. Explicit analytic test
conditions are retained; no perimeter inequality is assumed. -/
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def verticalGaussianStein (f : Space d × ℝ → ℝ) (z : Space d × ℝ) : ℝ :=
  deriv (fun t : ℝ => f (z.1,t)) z.2-z.2*f z

theorem gaussian_epigraph_vertical_weighted_flux
    (g : Space d → ℝ) (hg : Measurable g) (f : Space d × ℝ → ℝ)
    (hf : ∀ y,ContDiff ℝ 1 (fun t : ℝ => f (y,t)))
    (hs : ∀ y,HasCompactSupport (fun t : ℝ => f (y,t)))
    (hi : Integrable ({z : Space d × ℝ | g z.1 < z.2}.indicator (verticalGaussianStein f))
      ((gaussian d).prod (gaussianReal 0 1))) :
    (∫ z,({z : Space d × ℝ | g z.1 < z.2}.indicator (verticalGaussianStein f)) z
      ∂(gaussian d).prod (gaussianReal 0 1)) =
      -(∫ y,standardDensity (g y)*f (y,g y) ∂gaussian d) := by
  rw [integral_prod _ hi]
  calc
    _ = ∫ y,-standardDensity (g y)*f (y,g y) ∂gaussian d := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        have he : (fun t : ℝ => ({z : Space d × ℝ | g z.1 < z.2}.indicator
            (verticalGaussianStein f)) (y,t)) =
            (Ioi (g y)).indicator (fun t => deriv (fun s : ℝ => f (y,s)) t-t*f (y,t)) := by
          funext t
          by_cases ht : g y<t <;> simp [ht,verticalGaussianStein]
        change (∫ t,({z : Space d × ℝ | g z.1 < z.2}.indicator
          (verticalGaussianStein f)) (y,t) ∂gaussianReal 0 1) = _
        rw [he,integral_indicator measurableSet_Ioi]
        exact gaussianReal_halfline_weighted_flux _ (hf y) (hs y) (g y)
    _ = _ := by rw [← integral_neg]; congr 1; funext y; ring

end GaussianMeasureBridge
