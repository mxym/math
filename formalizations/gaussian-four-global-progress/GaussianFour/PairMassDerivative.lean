import GaussianFour.PairSliceIntegral
import GaussianFour.FacetCoordinates

/-! Actual competitor-price derivatives without affine independence. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

theorem positive_pairChart_mass_derivative
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l)) :
    HasDerivAt (fun t => winningMass v (coordinateShift b j t) i)
      (pairChartWeight v b i j) 0 := by
  let g : Space d → ℝ := fun y =>
    (affineMask (facetIndices i j) (facetNormal v i j) (facetOffset v b i j)).indicator
      (fun y => standardDensity (pairHeight v b i j y)) y / pairDen v i j
  have hg : Integrable g (gaussian d) := by
    simpa only [g, pairHeight] using
      (integrable_affineDensity (facetIndices i j) (facetNormal v i j)
        (facetOffset v b i j) (pairSlope v i j) (pairPrice v b i j)).div_const (pairDen v i j)
  have hdiff : ∀ᵐ y ∂gaussian d, HasDerivAt (fun t => pairSliceValue v b i j t y) (g y) 0 := by
    filter_upwards [ae_pairSliceMask_density_continuous v b i j hij hden.ne' hmass] with y hy
    have h := pairSliceValue_hasDerivAt v b i j y hy
    rw [pairSlice_boundary_density] at h
    exact h
  have hl (y : Space d) : LipschitzWith (Real.nnabs (standardDensity 0 / pairDen v i j))
      (fun t => pairSliceValue v b i j t y) := by
    have he : Real.nnabs (standardDensity 0 / pairDen v i j) =
        ⟨standardDensity 0 / pairDen v i j, div_nonneg (standardDensity_pos 0).le hden.le⟩ := by
      apply Subtype.ext
      change |standardDensity 0 / pairDen v i j| = standardDensity 0 / pairDen v i j
      exact abs_of_nonneg (div_nonneg (standardDensity_pos 0).le hden.le)
    rw [he]
    exact pairSliceValue_lipschitz v b i j hden y
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := gaussian d) (F := fun t y => pairSliceValue v b i j t y) (F' := g)
    (bound := fun _ => standardDensity 0 / pairDen v i j) (s := Set.univ) (x₀ := 0)
    (by simp) (Eventually.of_forall fun t =>
      (measurable_pairSliceValue v b i j hij hden t).aestronglyMeasurable)
    (integrable_pairSliceValue v b i j hij hden 0) hg.aestronglyMeasurable
    (ae_of_all _ fun y => (hl y).lipschitzOnWith) (integrable_const _) hdiff
  have he : (∫ y, g y ∂gaussian d) = pairChartWeight v b i j := by
    dsimp only [g]
    simp only [div_eq_mul_inv, integral_mul_const]
    rw [integral_indicator (measurableSet_affineMask _ _ _)]
    simp only [pairChartWeight, pairChartDensity, affineDensityIntegral, pairHeight,
      abs_of_pos hden, div_eq_mul_inv]
  rw [he] at h
  convert h.2 using 1
  funext t
  exact winningMass_eq_pairSliceIntegral v b i j hij hden t

end GaussianFour
