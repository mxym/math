import GaussianFour.WinningSeparation

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge

namespace GaussianFour

variable {d : ℕ}

lemma four_separation_constant_pos : 0 < Real.sqrt (2*Real.pi)/16 := by positivity

/-- Norm separation survives limits of the actual cell moments. Neither
convergence nor nondegeneracy of the limiting score normals is assumed. -/
theorem limit_winning_moments_separated
    (v : ℕ → Fin 4 → Space d) (b : ℕ → Fin 4 → ℝ)
    (hv : ∀ q, Function.Injective (v q))
    (hmass : ∀ q i, (gaussian d).real (winningCell (v q) (b q) i) = 1/4)
    (m : Fin 4 → Space d)
    (hlim : ∀ i, Tendsto (fun q => (winningPartition (v q) (b q) (hv q)).moment i)
      atTop (𝓝 (m i)))
    (i j : Fin 4) (hij : i ≠ j) :
    Real.sqrt (2*Real.pi)/16 ≤ ‖m i-m j‖ := by
  exact le_of_tendsto ((hlim i).sub (hlim j)).norm
    (Eventually.of_forall fun q =>
      balanced_four_winning_moment_norm_separation (v q) (b q) (hv q) (hmass q) i j hij)

/-- Actual balanced four-cell moments stay pairwise distinct at every
convergent limit, even if the inducing covariance tends to the boundary. -/
theorem limit_winning_moments_injective
    (v : ℕ → Fin 4 → Space d) (b : ℕ → Fin 4 → ℝ)
    (hv : ∀ q, Function.Injective (v q))
    (hmass : ∀ q i, (gaussian d).real (winningCell (v q) (b q) i) = 1/4)
    (m : Fin 4 → Space d)
    (hlim : ∀ i, Tendsto (fun q => (winningPartition (v q) (b q) (hv q)).moment i)
      atTop (𝓝 (m i))) : Function.Injective m := by
  intro i j he
  by_contra hij
  have h := limit_winning_moments_separated v b hv hmass m hlim i j hij
  rw [he,sub_self,norm_zero] at h
  exact (not_le_of_gt four_separation_constant_pos) h

/-- The limiting self-moment relation forces distinct limiting scores.
This is the non-coalescence step, not an assumption of a regular boundary. -/
theorem limit_self_moment_scores_injective
    (v : ℕ → Fin 4 → Space d) (b : ℕ → Fin 4 → ℝ)
    (hv : ∀ q, Function.Injective (v q))
    (hmass : ∀ q i, (gaussian d).real (winningCell (v q) (b q) i) = 1/4)
    (m w : Fin 4 → Space d) (μ : ℝ)
    (hlim : ∀ i, Tendsto (fun q => (winningPartition (v q) (b q) (hv q)).moment i)
      atTop (𝓝 (m i)))
    (hself : ∀ i, m i = μ • w i) : Function.Injective w := by
  intro i j he
  apply limit_winning_moments_injective v b hv hmass m hlim
  rw [hself i,hself j,he]

lemma residual_pair_sq_le (e : Fin 4 → Space d) (i j : Fin 4) (hij : i ≠ j) :
    ‖e i-e j‖^2 ≤ 2*∑ l, ‖e l‖^2 := by
  classical
  have hs : ‖e i‖^2+‖e j‖^2 ≤ ∑ l, ‖e l‖^2 := by
    have hle : (∑ l ∈ ({i,j} : Finset (Fin 4)), ‖e l‖^2) ≤ ∑ l, ‖e l‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro l _ _
      exact sq_nonneg _
    simpa only [Finset.sum_pair hij] using hle
  have htriangle := norm_sub_le (e i) (e j)
  have hsq := sq_le_sq₀ (norm_nonneg (e i-e j)) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr htriangle
  nlinarith [sq_nonneg (‖e i‖-‖e j‖)]

/-- Equation (22) of the four-cell manuscript, derived for actual Gaussian
moments from the squared residual estimate. The residual estimate is an
explicit analytic premise; no spectral theorem is silently postulated. -/
theorem winning_score_separation_of_residual
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1/4)
    (μ ε : ℝ) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hres : (∑ l, ‖(winningPartition v b hv).moment l-μ • v l‖^2) ≤ ε*μ^2)
    (i j : Fin 4) (hij : i ≠ j) :
    Real.sqrt (2*Real.pi)/16 ≤ μ*(‖v i-v j‖+Real.sqrt (2*ε)) := by
  let m := (winningPartition v b hv).moment
  let e : Fin 4 → Space d := fun l => m l-μ • v l
  have hpair := residual_pair_sq_le e i j hij
  have hsqr : (Real.sqrt (2*ε))^2 = 2*ε := Real.sq_sqrt (by positivity)
  have he : ‖e i-e j‖ ≤ μ*Real.sqrt (2*ε) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hμ (Real.sqrt_nonneg _))).mp
    have hupper : ‖e i-e j‖^2 ≤ 2*(ε*μ^2) := hpair.trans (mul_le_mul_of_nonneg_left hres (by norm_num))
    nlinarith [sq_nonneg μ]
  have heq : m i-m j = μ • (v i-v j)+(e i-e j) := by
    dsimp [e]
    rw [smul_sub]
    abel
  have hnorm : ‖m i-m j‖ ≤ μ*‖v i-v j‖+μ*Real.sqrt (2*ε) := by
    rw [heq]
    have h := norm_add_le (μ • (v i-v j)) (e i-e j)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ] at h
    linarith
  have hsep := balanced_four_winning_moment_norm_separation v b hv hmass i j hij
  change Real.sqrt (2*Real.pi)/16 ≤ ‖m i-m j‖ at hsep
  nlinarith

end GaussianFour
