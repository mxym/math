import GaussianBalancedValue

/-! Differentiation of actual Gaussian score-price integrals in simultaneous
score and price directions. No covariance derivative or facet formula is assumed. -/
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def affineScores (v h : Fin k → Space d) (t : ℝ) : Fin k → Space d :=
  fun i => v i + t • h i

noncomputable def affinePrices (b q : Fin k → ℝ) (t : ℝ) : Fin k → ℝ :=
  fun i => b i + t * q i

@[simp] lemma affineScores_zero (v h : Fin k → Space d) : affineScores v h 0 = v := by
  ext i; simp [affineScores]

@[simp] lemma affinePrices_zero (b q : Fin k → ℝ) : affinePrices b q 0 = b := by
  ext i; simp [affinePrices]

lemma directional_score_abs_le (h : Fin k → Space d) (q : Fin k → ℝ) (x : Space d)
    (i : Fin k) : |⟪h i, x⟫ - q i| ≤ ‖h‖ * ‖x‖ + ‖q‖ := by
  calc
    |⟪h i, x⟫ - q i| ≤ |⟪h i, x⟫| + |q i| := abs_sub _ _
    _ ≤ ‖h i‖ * ‖x‖ + ‖q i‖ := by
      rw [← Real.norm_eq_abs (q i)]
      exact add_le_add (abs_real_inner_le_norm (h i) x) le_rfl
    _ ≤ ‖h‖ * ‖x‖ + ‖q‖ := add_le_add
      (mul_le_mul_of_nonneg_right (norm_le_pi_norm h i) (norm_nonneg x)) (norm_le_pi_norm q i)

lemma affineScore_le (v h : Fin k → Space d) (b q : Fin k → ℝ)
    (x : Space d) (s t : ℝ) :
    scoreMax (affineScores v h s) (affinePrices b q s) x ≤
      scoreMax (affineScores v h t) (affinePrices b q t) x +
      |s - t| * (‖h‖ * ‖x‖ + ‖q‖) := by
  unfold scoreMax
  refine Finset.sup'_le _ _ fun i _ => ?_
  change ⟪affineScores v h s i, x⟫ - affinePrices b q s i ≤
    scoreMax (affineScores v h t) (affinePrices b q t) x + _
  have hmax := le_scoreMax (affineScores v h t) (affinePrices b q t) x i
  have hslope : (s-t) * (⟪h i, x⟫ - q i) ≤
      |s-t| * (‖h‖ * ‖x‖ + ‖q‖) := by
    calc
      (s-t) * (⟪h i, x⟫ - q i) ≤ |(s-t) * (⟪h i, x⟫ - q i)| := le_abs_self _
      _ = |s-t| * |⟪h i, x⟫ - q i| := abs_mul _ _
      _ ≤ |s-t| * (‖h‖ * ‖x‖ + ‖q‖) := mul_le_mul_of_nonneg_left
        (directional_score_abs_le h q x i) (abs_nonneg _)
  simp only [affineScores, affinePrices, inner_add_left, real_inner_smul_left] at hmax ⊢
  nlinarith

lemma affineScore_lipschitz (v h : Fin k → Space d) (b q : Fin k → ℝ) (x : Space d) :
    LipschitzWith (Real.nnabs (‖h‖ * ‖x‖ + ‖q‖))
      (fun t => scoreMax (affineScores v h t) (affinePrices b q t) x) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have hst := affineScore_le v h b q x s t
  have hts := affineScore_le v h b q x t s
  rw [abs_sub_comm t s] at hts
  have hk : 0 ≤ ‖h‖ * ‖x‖ + ‖q‖ := by positivity
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hk]
  rw [mul_comm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma affineScore_hasDerivAt (v h : Fin k → Space d) (b q : Fin k → ℝ)
    (x : Space d) (r : Fin k) (hr : x ∈ winningCell v b r) :
    HasDerivAt (fun t => scoreMax (affineScores v h t) (affinePrices b q t) x)
      (⟪h r, x⟫ - q r) 0 := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ),
      x ∈ winningCell (affineScores v h t) (affinePrices b q t) r := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = r
    · exact Eventually.of_forall fun _ hh => False.elim (hh hj)
    · have hjc : ContinuousAt
          (fun t => ⟪affineScores v h t j, x⟫ - affinePrices b q t j) 0 := by
        unfold affineScores affinePrices; fun_prop
      have hrc : ContinuousAt
          (fun t => ⟪affineScores v h t r, x⟫ - affinePrices b q t r) 0 := by
        unfold affineScores affinePrices; fun_prop
      exact (hjc.eventually_lt hrc (by simpa using hr j hj)).mono fun _ ht _ => ht
  have heq : (fun t => scoreMax (affineScores v h t) (affinePrices b q t) x)
      =ᶠ[𝓝 (0 : ℝ)] (fun t => ⟪affineScores v h t r, x⟫ - affinePrices b q t r) :=
    hevent.mono fun _ ht => scoreMax_eq_winning_score _ _ x r ht
  have hd : HasDerivAt (fun t => ⟪affineScores v h t r, x⟫ - affinePrices b q t r)
      (⟪h r, x⟫ - q r) 0 := by
    simp only [affineScores, affinePrices, inner_add_left, real_inner_smul_left]
    convert ((hasDerivAt_const 0 ⟪v r, x⟫).add
      ((hasDerivAt_id 0).mul_const ⟪h r, x⟫)).sub
      ((hasDerivAt_const 0 (b r)).add ((hasDerivAt_id 0).mul_const (q r))) using 1
    · rfl
    · simp
  exact hd.congr_of_eventuallyEq heq

/-- Joint score/price differentiation under the actual Gaussian integral.
The derivative consists of genuine Bochner winning-cell moments and masses. -/
theorem expectedScore_directional_derivative (v h : Fin k → Space d)
    (b q : Fin k → ℝ) (hv : Function.Injective v) :
    HasDerivAt (fun t => expectedScore (affineScores v h t) (affinePrices b q t))
      ((∑ i, ⟪h i, (winningPartition v b hv).moment i⟫) -
        ∑ i, (winningPartition v b hv).mass i * q i) 0 := by
  classical
  let F := winningPartition v b hv
  let g : Space d → ℝ := fun x => ∑ i, F.labels i x * (⟪h i, x⟫ - q i)
  have hgint : Integrable g (gaussian d) :=
    integrable_finsetSum _ (fun i _ => F.integrable_weighted_score i (h i) (q i))
  have hdiff : ∀ᵐ x ∂gaussian d, HasDerivAt
      (fun t => scoreMax (affineScores v h t) (affinePrices b q t) x) (g x) 0 := by
    filter_upwards [ae_unique_winner v b hv] with x hx
    obtain ⟨r, hr⟩ := hx
    have hnot : ∀ j, j ≠ r → x ∉ winningCell v b j := by
      intro j hj hxj
      exact Set.disjoint_left.mp (winningCell_disjoint v b j r hj) hxj hr
    have he : g x = ⟪h r, x⟫ - q r := by
      dsimp [g]
      rw [Finset.sum_eq_single r]
      · simp [F, winningPartition, hr]
      · intro j _ hj; simp [F, winningPartition, hnot j hj]
      · simp
    rw [he]
    exact affineScore_hasDerivAt v h b q x r hr
  have result := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := gaussian d)
    (F := fun t x => scoreMax (affineScores v h t) (affinePrices b q t) x)
    (F' := g) (bound := fun x => ‖h‖ * ‖x‖ + ‖q‖) (s := Set.univ) (x₀ := 0)
    (by simp) (Eventually.of_forall fun t => (continuous_scoreMax _ _).aestronglyMeasurable)
    (by simpa using integrable_scoreMax v b) hgint.aestronglyMeasurable
    (ae_of_all _ fun x => (affineScore_lipschitz v h b q x).lipschitzOnWith)
    (((IsGaussian.integrable_id (μ := gaussian d)).norm.const_mul ‖h‖).add (integrable_const ‖q‖))
    hdiff
  have heval : (∫ x, g x ∂gaussian d) =
      (∑ i, ⟪h i, F.moment i⟫) - ∑ i, F.mass i * q i := by
    rw [show g = (fun x => ∑ i, F.labels i x * (⟪h i, x⟫ - q i)) from rfl,
      integral_finsetSum Finset.univ (fun i _ => F.integrable_weighted_score i (h i) (q i))]
    simp_rw [F.integral_weighted_score]
    rw [Finset.sum_sub_distrib]
  rw [heval] at result
  exact result.2

end GaussianMeasureBridge
