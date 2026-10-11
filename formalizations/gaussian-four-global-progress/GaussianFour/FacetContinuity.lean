import GaussianFour.FacetChart

/-! Joint continuity of actual Gaussian facet-chart integrals. The only
geometric hypotheses are a valid coordinate chart and positive actual cell
masses at the limiting diagram; no affine independence is assumed. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

abbrev ChartParameters (d k : ℕ) :=
  (Fin k → Space (d+1)) × (Fin k → ℝ)

lemma continuous_pairDen (i j : Fin k) :
    Continuous (fun v : Fin k → Space (d+1) => pairDen v i j) := by
  unfold pairDen
  fun_prop

lemma continuous_tailCoordinates : Continuous (tailCoordinates (d := d)) := by
  unfold tailCoordinates
  fun_prop

lemma continuousAt_pairSlope (v : Fin k → Space (d+1)) (i j : Fin k)
    (hden : pairDen v i j ≠ 0) :
    ContinuousAt (fun u => pairSlope u i j) v := by
  unfold pairSlope
  exact ((continuous_pairDen i j).continuousAt.inv₀ hden).smul
    (((continuous_tailCoordinates.comp (continuous_apply j)).continuousAt).sub
      ((continuous_tailCoordinates.comp (continuous_apply i)).continuousAt))

lemma continuousAt_pairPrice (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (hden : pairDen v i j ≠ 0) :
    ContinuousAt (fun z : ChartParameters d k => pairPrice z.1 z.2 i j) (v,b) := by
  unfold pairPrice
  exact (show ContinuousAt (fun z : ChartParameters d k => z.2 j - z.2 i) (v,b)
      from by fun_prop).div
    ((continuous_pairDen i j).comp continuous_fst).continuousAt hden

/-- Facet-density continuity includes rank-deficient limiting score diagrams. -/
theorem continuousAt_pairChartDensity (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (hden : pairDen v i j ≠ 0)
    (hmass : ∀ t, 0 < (gaussian (d+1)).real (winningCell v b t)) :
    ContinuousAt (fun z : ChartParameters d k => pairChartDensity z.1 z.2 i j) (v,b) := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hden (by simp [pairDen])
  have ht (l : Fin k) :
      ContinuousAt (fun z : ChartParameters d k => tailCoordinates (z.1 l)) (v,b) := by
    unfold tailCoordinates
    fun_prop
  have hd : ContinuousAt (fun z : ChartParameters d k => pairDen z.1 i j) (v,b) := by
    unfold pairDen
    fun_prop
  have hs : ContinuousAt (fun z : ChartParameters d k => pairSlope z.1 i j) (v,b) := by
    unfold pairSlope
    exact (hd.inv₀ hden).smul ((ht j).sub (ht i))
  have hp := continuousAt_pairPrice v b i j hden
  have hnormal (l : Fin k) :
      ContinuousAt (fun z : ChartParameters d k => facetNormal z.1 i j l) (v,b) := by
    unfold facetNormal
    exact ((ht i).sub (ht l)).add
      ((show ContinuousAt (fun z : ChartParameters d k => z.1 i 0 - z.1 l 0) (v,b)
        from by fun_prop).smul hs)
  have hoffset (l : Fin k) :
      ContinuousAt (fun z : ChartParameters d k => facetOffset z.1 z.2 i j l) (v,b) := by
    unfold facetOffset
    exact (show ContinuousAt (fun z : ChartParameters d k => z.2 i - z.2 l) (v,b)
        from by fun_prop).add
      ((show ContinuousAt (fun z : ChartParameters d k => z.1 i 0 - z.1 l 0) (v,b)
        from by fun_prop).mul hp)
  apply continuousAt_affineDensityIntegral (facetIndices i j)
    (fun z : ChartParameters d k => facetNormal z.1 i j)
    (fun z : ChartParameters d k => facetOffset z.1 z.2 i j)
    (fun z => pairSlope z.1 i j) (fun z => pairPrice z.1 z.2 i j) (v,b)
    (fun l _ => hnormal l) (fun l _ => hoffset l) hs hp
  intro l hl
  have he : l ≠ i ∧ l ≠ j := by simpa [facetIndices] using hl
  exact facet_restriction_nonzero v b i j l hij (Ne.symm he.1) (Ne.symm he.2) hden hmass

/-- Dividing by the normal coordinate preserves continuity in a valid chart. -/
theorem continuousAt_pairChartWeight (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (hden : pairDen v i j ≠ 0)
    (hmass : ∀ t, 0 < (gaussian (d+1)).real (winningCell v b t)) :
    ContinuousAt (fun z : ChartParameters d k => pairChartWeight z.1 z.2 i j) (v,b) := by
  exact (continuousAt_pairChartDensity v b i j hden hmass).div
    (((continuous_pairDen i j).comp continuous_fst).continuousAt.abs)
    (abs_ne_zero.mpr hden)

/-- The four-cell specialization derives the boundary nondegeneracy from the
original mass constraints, including at rank-one and rank-two limits. -/
theorem balanced_four_pairChartWeight_continuous
    (v : Fin 4 → Space (d+1)) (b : Fin 4 → ℝ) (i j : Fin 4)
    (hden : pairDen v i j ≠ 0)
    (hmass : ∀ t, (gaussian (d+1)).real (winningCell v b t) = 1/4) :
    ContinuousAt (fun z : ChartParameters d 4 => pairChartWeight z.1 z.2 i j) (v,b) :=
  continuousAt_pairChartWeight v b i j hden
    (fun t => by rw [hmass t]; norm_num)

end GaussianFour
