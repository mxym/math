import GaussianPrimalDual

/-! The actual balanced Gaussian score value, including degenerate score families.
The definition is an infimum of genuine Gaussian integrals, not an abstract
function with continuity or homogeneity supplied as hypotheses. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def balancedValue (v : Fin k → Space d) (p : Fin k → ℝ) : ℝ :=
  sInf (Set.range (priceObjective v p))

lemma balancedValue_eq_of_minimizer (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hb : ∀ c, priceObjective v p b ≤ priceObjective v p c) :
    balancedValue v p = priceObjective v p b := by
  exact IsLeast.csInf_eq ⟨⟨b, rfl⟩, by rintro _ ⟨c, rfl⟩; exact hb c⟩

theorem balancedValue_attained (v : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ b, balancedValue v p = priceObjective v p b ∧
      ∀ c, priceObjective v p b ≤ priceObjective v p c := by
  obtain ⟨b, hb⟩ := exists_price_minimizer v p hp hs
  exact ⟨b, balancedValue_eq_of_minimizer v p b hb, hb⟩

lemma balancedValue_le_objective (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    balancedValue v p ≤ priceObjective v p b := by
  obtain ⟨c, hc, hm⟩ := balancedValue_attained v p hp hs
  rw [hc]
  exact hm b

lemma priceObjective_nonneg (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 ≤ priceObjective v p b := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_min b
  rw [← priceObjective_sub_const v p b hs (b i)]
  have h := expectedScore_nonneg_of_zero v (fun j => b j - b i) i (sub_self _)
  exact add_nonneg h (Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (sub_nonneg.mpr (hi j)))

theorem balancedValue_nonneg (v : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) : 0 ≤ balancedValue v p := by
  obtain ⟨b, hb, _⟩ := balancedValue_attained v p hp hs
  rw [hb]
  exact priceObjective_nonneg v p b (fun i => (hp i).le) hs

/-- The price bound applies even when some or all score rows coincide. -/
theorem partitionValue_le_balancedValue (v : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (F : FractionalPartition d k) (hF : ∀ i, F.mass i = p i) :
    partitionValue v F ≤ balancedValue v p := by
  obtain ⟨b, hb, _⟩ := balancedValue_attained v p hp hs
  rw [hb]
  have h := F.price_dual v b
  simpa only [partitionValue, priceObjective, expectedScore, hF] using h

lemma scoreMax_le_scoreMax_add (v w : Fin k → Space d) (b : Fin k → ℝ)
    (x : Space d) : scoreMax v b x ≤ scoreMax w b x + ‖v - w‖ * ‖x‖ := by
  unfold scoreMax
  refine Finset.sup'_le _ _ fun i _ => ?_
  change ⟪v i, x⟫ - b i ≤ scoreMax w b x + ‖v - w‖ * ‖x‖
  have h := le_scoreMax w b x i
  have hinner : ⟪v i - w i, x⟫ ≤ ‖v - w‖ * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_le_pi_norm (v - w) i) (norm_nonneg x))
  rw [inner_sub_left] at hinner
  linarith

noncomputable def gaussianMeanNorm (d : ℕ) : ℝ := ∫ x : Space d, ‖x‖ ∂gaussian d

lemma gaussianMeanNorm_nonneg (d : ℕ) : 0 ≤ gaussianMeanNorm d :=
  integral_nonneg fun _ => norm_nonneg _

lemma priceObjective_le_add_score_norm (v w : Fin k → Space d) (p b : Fin k → ℝ) :
    priceObjective v p b ≤ priceObjective w p b + ‖v - w‖ * gaussianMeanNorm d := by
  have hi : Integrable (fun x : Space d => ‖x‖) (gaussian d) :=
    (IsGaussian.integrable_id (μ := gaussian d)).norm
  have h := integral_mono (integrable_scoreMax v b)
    ((integrable_scoreMax w b).add
      (hi.const_mul ‖v - w‖))
    (scoreMax_le_scoreMax_add v w b)
  dsimp only [Pi.add_apply, id_eq] at h
  rw [integral_add (integrable_scoreMax w b)
    (hi.const_mul ‖v - w‖),
    integral_const_mul] at h
  unfold priceObjective expectedScore gaussianMeanNorm
  linarith

/-- A uniform estimate in the price variable gives continuity up to collisions
of score rows; no differentiability or tie-null assumption is needed. -/
theorem balancedValue_abs_sub_le (v w : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    |balancedValue v p - balancedValue w p| ≤ ‖v - w‖ * gaussianMeanNorm d := by
  have hbound : ∀ v w : Fin k → Space d,
      balancedValue v p ≤ balancedValue w p + ‖v - w‖ * gaussianMeanNorm d := by
    intro v w
    obtain ⟨b, hb, _⟩ := balancedValue_attained w p hp hs
    exact (balancedValue_le_objective v p b hp hs).trans (by
      rw [hb]; exact priceObjective_le_add_score_norm v w p b)
  have h₁ := hbound v w
  have h₂ := hbound w v
  rw [norm_sub_rev w v] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem balancedValue_lipschitz (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    LipschitzWith ⟨gaussianMeanNorm d, gaussianMeanNorm_nonneg d⟩
      (fun v : Fin k → Space d => balancedValue v p) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  change |balancedValue v p - balancedValue w p| ≤ gaussianMeanNorm d * ‖v - w‖
  rw [mul_comm]
  exact balancedValue_abs_sub_le v w p hp hs

theorem continuous_balancedValue (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    Continuous (fun v : Fin k → Space d => balancedValue v p) :=
  (balancedValue_lipschitz p hp hs).continuous

end GaussianMeasureBridge
