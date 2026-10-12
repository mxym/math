import GaussianFour.FacetGraphBridge
import GaussianFour.PriceBounds
import GaussianSimplicialMassFlux

/-! A fixed orthogonal chart exists for every distinct pair of inducing
scores. The chart is chosen once at the limit, not assumed to move smoothly. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

/-- Householder coordinates make any nonzero score difference point in the
positive first-coordinate direction. -/
theorem exists_positive_pair_chart (v : Fin k → Space (d+1)) (i j : Fin k)
    (hij : v i ≠ v j) :
    ∃ T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1),
      pairDen (fun l => T (v l)) i j = ‖v i - v j‖ := by
  let w := v i - v j
  have hw : w ≠ 0 := sub_ne_zero.mpr hij
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  let z : Space (d+1) := ‖w‖⁻¹ • w
  let e : Space (d+1) := EuclideanSpace.basisFun (Fin (d+1)) ℝ 0
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
    exact inv_mul_cancel₀ hn
  have he : ‖e‖ = 1 := by simp [e]
  let T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1) := (ℝ ∙ (z-e))ᗮ.reflection
  have hT : T z = e := Submodule.reflection_sub (hz.trans he.symm)
  have hwz : ‖w‖ • z = w := by simp [z, smul_smul, mul_inv_cancel₀ hn]
  have hTw : T w = ‖w‖ • e := by
    calc
      T w = T (‖w‖ • z) := congrArg T hwz.symm
      _ = ‖w‖ • e := by rw [map_smul, hT]
  refine ⟨T, ?_⟩
  calc
    pairDen (fun l => T (v l)) i j = (T w) 0 := by
      simp only [pairDen, w, map_sub, PiLp.sub_apply]
    _ = (‖w‖ • e) 0 := congrArg (fun x : Space (d+1) => x 0) hTw
    _ = ‖v i - v j‖ := by simp [e, w]

variable [NeZero k]

/-- Every pair of actual positive-mass Gaussian cells admits a fixed orthogonal
chart in which its Gaussian facet integral depends continuously on the original
scores and prices. This includes singular limiting configurations. -/
theorem exists_continuous_pair_chart_of_positive_masses
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ t, 0 < (gaussian (d+1)).real (winningCell v b t))
    (i j : Fin k) (hij : i ≠ j) :
    ∃ T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1),
      0 < pairDen (fun l => T (v l)) i j ∧
      ContinuousAt (fun z : ChartParameters d k =>
        pairChartWeight (fun l => T (z.1 l)) z.2 i j) (v,b) := by
  have hv := injective_scores_of_positive_winning_masses v b hmass
  have hdiff : v i ≠ v j := fun h => hij (hv h)
  obtain ⟨T, hT⟩ := exists_positive_pair_chart v i j hdiff
  have hp : 0 < pairDen (fun l => T (v l)) i j := by
    rw [hT]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hdiff)
  have hm (t : Fin k) :
      0 < (gaussian (d+1)).real (winningCell (fun l => T (v l)) b t) := by
    change 0 < winningMass (fun l => T (v l)) b t
    rw [winningMass_isometry]
    exact hmass t
  have hc := continuousAt_pairChartWeight (fun l => T (v l)) b i j hp.ne' hm
  have hf : ContinuousAt (fun z : ChartParameters d k =>
      ((fun l => T (z.1 l)), z.2)) (v,b) := by fun_prop
  refine ⟨T, hp, ?_⟩
  exact ContinuousAt.comp
    (f := fun z : ChartParameters d k => ((fun l => T (z.1 l)), z.2))
    (g := fun z : ChartParameters d k => pairChartWeight z.1 z.2 i j)
    hc hf

end GaussianFour
