import GaussianBoundedDirectionalStein
import GaussianWinningContinuity

/-! Actual Gaussian directional derivative integrals of the smooth winning
approximants converge to the corresponding actual cell moments. No face
regularity or surface-measure formula is assumed. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma rawWinningMoment_inner (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (u : Space d) :
    (∫ x,(winningCell v b i).indicator (fun x => ⟪u,x⟫) x ∂gaussian d) =
      ⟪u,rawWinningMoment v b i⟫ := by
  have hi := (IsGaussian.integrable_id (μ := gaussian d)).indicator (measurableSet_winningCell v b i)
  have he := (innerSL ℝ u).integral_comp_comm hi
  change _ = (innerSL ℝ u) (∫ x,(winningCell v b i).indicator id x ∂gaussian d)
  convert he using 1
  congr 1
  funext x
  by_cases hx : x ∈ winningCell v b i <;> simp [hx]

theorem smoothWinningApprox_inner_integral_tendsto
    (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) (u : Space d) :
    Tendsto (fun N => ∫ x,⟪u,x⟫*smoothWinningApprox v b i N x ∂gaussian d) atTop
      (𝓝 ⟪u,rawWinningMoment v b i⟫) := by
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun x : Space d => ⟪u,x⟫*smoothWinningApprox v b i N x) (gaussian d) :=
    ((innerSL ℝ u).continuous.mul (smoothWinningApprox_contDiff v b i N).continuous).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ x ∂gaussian d,
      ‖⟪u,x⟫*smoothWinningApprox v b i N x‖ ≤ ‖⟪u,x⟫‖ := ae_of_all _ fun x => by
    rw [norm_mul,Real.norm_eq_abs (smoothWinningApprox v b i N x),
      abs_of_nonneg (smoothWinningApprox_bounds v b i N x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (smoothWinningApprox_bounds v b i N x).2
  have hp : ∀ᵐ x ∂gaussian d,
      Tendsto (fun N => ⟪u,x⟫*smoothWinningApprox v b i N x) atTop
        (𝓝 ((winningCell v b i).indicator (fun x => ⟪u,x⟫) x)) := ae_of_all _ fun x => by
    have hh := (tendsto_const_nhds (x := ⟪u,x⟫)).mul (smoothWinningApprox_tendsto v b i x)
    convert hh using 1
    by_cases hx : x ∈ winningCell v b i <;> simp [hx]
  have ht := tendsto_integral_of_dominated_convergence (fun x : Space d => ‖⟪u,x⟫‖)
    hm (integrable_gaussian_inner u).norm hb hp
  simpa only [rawWinningMoment_inner] using ht

theorem smoothWinningApprox_directional_integral_tendsto
    (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) (u : Space d) :
    Tendsto (fun N => ∫ x,fderiv ℝ (smoothWinningApprox v b i N) x u ∂gaussian d) atTop
      (𝓝 ⟪u,rawWinningMoment v b i⟫) := by
  apply (smoothWinningApprox_inner_integral_tendsto v b i u).congr'
  exact Eventually.of_forall fun N => by
    obtain ⟨B,_,hB⟩ := smoothWinningApprox_gradient_bound v b i N
    exact (gaussian_bounded_directional_stein _ (smoothWinningApprox_contDiff v b i N)
      (smoothWinningApprox_bounds v b i N) B hB u).symm

end GaussianMeasureBridge
