import GaussianFractionalEquality

/-! The attained balanced assignment value on actual Gaussian score lists.
All ranks, including coincident score vectors, are allowed in the value and
continuity statements. No covariance sharp comparison is assumed. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianFourGlobal
open GaussianMeasureBridge

noncomputable def uniformPartition (d : ℕ) : FractionalPartition d 4 where
  labels _ _ := 1 / 4
  measurable_labels _ := measurable_const
  nonneg _ := ae_of_all _ fun _ => by norm_num
  le_one _ := ae_of_all _ fun _ => by norm_num
  sum_one := ae_of_all _ fun _ => by norm_num

lemma uniformPartition_mass (d : ℕ) (i : Fin 4) : (uniformPartition d).mass i = 1 / 4 := by
  simp [uniformPartition, FractionalPartition.mass]

lemma uniformPartition_moment (d : ℕ) (i : Fin 4) : (uniformPartition d).moment i = 0 := by
  change (∫ x : Space d, (1 / 4 : ℝ) • x ∂gaussian d) = 0
  rw [integral_smul]
  change (1 / 4 : ℝ) • (∫ x : Space d, x ∂stdGaussian (Space d)) = 0
  rw [integral_id_stdGaussian, smul_zero]

/-- The genuine infimum of the actual Gaussian price objective. -/
noncomputable def balancedValue {d : ℕ} (v : Fin 4 → Space d) : ℝ :=
  sInf (range (priceObjective v (fun _ => 1 / 4)))

lemma balancedValue_eq_minimizer {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (hb : ∀ c, priceObjective v (fun _ => 1 / 4) b ≤ priceObjective v (fun _ => 1 / 4) c) :
    balancedValue v = priceObjective v (fun _ => 1 / 4) b := by
  have hbelow : BddBelow (range (priceObjective v (fun _ => 1 / 4))) := by
    refine ⟨priceObjective v (fun _ => 1 / 4) b, ?_⟩
    rintro y ⟨c, rfl⟩
    exact hb c
  apply le_antisymm
  · exact csInf_le hbelow ⟨b, rfl⟩
  · apply le_csInf (range_nonempty _)
    rintro y ⟨c, rfl⟩
    exact hb c

/-- Attainment is derived from the proved price-existence theorem, even when
scores coincide; no deterministic winning assignment is asserted in that case. -/
theorem balancedValue_attained {d : ℕ} (v : Fin 4 → Space d) :
    ∃ b : Fin 4 → ℝ, balancedValue v = priceObjective v (fun _ => 1 / 4) b ∧
      ∀ c, priceObjective v (fun _ => 1 / 4) b ≤ priceObjective v (fun _ => 1 / 4) c := by
  obtain ⟨b, hb⟩ := exists_price_minimizer v (fun _ => 1 / 4)
    (fun _ => by norm_num) (by norm_num)
  exact ⟨b, balancedValue_eq_minimizer v b hb, hb⟩

theorem balancedValue_le_price {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ) :
    balancedValue v ≤ priceObjective v (fun _ => 1 / 4) b := by
  obtain ⟨c, hc, hm⟩ := balancedValue_attained v
  rw [hc]
  exact hm b

/-- The feasible-assignment inequality after taking the price infimum. -/
theorem fractional_value_le_balancedValue {d : ℕ} (F : FractionalPartition d 4)
    (hF : ∀ i, F.mass i = 1 / 4) (v : Fin 4 → Space d) :
    partitionValue v F ≤ balancedValue v := by
  obtain ⟨b, hb, _⟩ := balancedValue_attained v
  rw [hb]
  have h := F.price_dual v b
  simp only [hF] at h
  exact h

theorem balancedValue_nonneg {d : ℕ} (v : Fin 4 → Space d) : 0 ≤ balancedValue v := by
  have h := fractional_value_le_balancedValue (uniformPartition d) (uniformPartition_mass d) v
  simpa only [partitionValue, uniformPartition_moment, inner_zero_right, Finset.sum_const_zero] using h

/-- The fixed finite Gaussian first radial moment, not an assumed Gaussian constant. -/
noncomputable def gaussianRadius (d : ℕ) : ℝ := ∫ x : Space d, ‖x‖ ∂gaussian d

lemma gaussianRadius_nonneg (d : ℕ) : 0 ≤ gaussianRadius d := integral_nonneg fun _ => norm_nonneg _

lemma scoreMax_score_le {d : ℕ} (v w : Fin 4 → Space d) (b : Fin 4 → ℝ) (x : Space d) :
    scoreMax v b x ≤ scoreMax w b x + ‖v - w‖ * ‖x‖ := by
  unfold scoreMax
  apply Finset.sup'_le
  intro i _
  change ⟪v i, x⟫ - b i ≤ scoreMax w b x + ‖v - w‖ * ‖x‖
  have hscore := le_scoreMax w b x i
  have hn : ‖v i - w i‖ ≤ ‖v - w‖ := norm_le_pi_norm (v - w) i
  have hi : ⟪v i, x⟫ - ⟪w i, x⟫ ≤ ‖v - w‖ * ‖x‖ := by
    rw [← inner_sub_left]
    exact (real_inner_le_norm (v i - w i) x).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg x))
  linarith

/-- A score perturbation estimate uniform in every price vector. -/
theorem expectedScore_score_le {d : ℕ} (v w : Fin 4 → Space d) (b : Fin 4 → ℝ) :
    expectedScore v b ≤ expectedScore w b + ‖v - w‖ * gaussianRadius d := by
  have hnorm : Integrable (fun x : Space d => ‖x‖) (gaussian d) := IsGaussian.integrable_id.norm
  have h := integral_mono (integrable_scoreMax v b)
    ((integrable_scoreMax w b).add (hnorm.const_mul ‖v - w‖))
    (scoreMax_score_le v w b)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_scoreMax w b) (hnorm.const_mul ‖v - w‖), integral_const_mul] at h
  exact h

theorem balancedValue_score_le {d : ℕ} (v w : Fin 4 → Space d) :
    balancedValue v ≤ balancedValue w + ‖v - w‖ * gaussianRadius d := by
  obtain ⟨b, hb, _⟩ := balancedValue_attained w
  have h1 := balancedValue_le_price v b
  have h2 := expectedScore_score_le v w b
  rw [hb]
  unfold priceObjective at *
  linarith

theorem balancedValue_abs_sub_le {d : ℕ} (v w : Fin 4 → Space d) :
    |balancedValue v - balancedValue w| ≤ ‖v - w‖ * gaussianRadius d := by
  have h1 := balancedValue_score_le v w
  have h2 := balancedValue_score_le w v
  rw [norm_sub_rev w v] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Global continuity, including every coincident-score and rank-deficient list. -/
theorem balancedValue_lipschitz (d : ℕ) :
    LipschitzWith ⟨gaussianRadius d, gaussianRadius_nonneg d⟩
      (balancedValue (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change ‖balancedValue v - balancedValue w‖ ≤ gaussianRadius d * ‖v - w‖
  simpa only [Real.norm_eq_abs, mul_comm] using balancedValue_abs_sub_le v w

theorem continuous_balancedValue (d : ℕ) : Continuous (balancedValue (d := d)) :=
  (balancedValue_lipschitz d).continuous

lemma expectedScore_zero_zero (d : ℕ) : expectedScore (0 : Fin 4 → Space d) 0 = 0 := by
  simp [expectedScore, scoreMax]

/-- A coarse but uniform price bound sufficient for compactness. The gauge
is explicit; balancing and actual zero Gaussian mean supply the estimate. -/
theorem balanced_price_bound {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (hv : Function.Injective v)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (hb0 : ∀ i, 0 ≤ b i) (hz : ∃ i, b i = 0) (i : Fin 4) :
    b i ≤ 4 * ‖v‖ * gaussianRadius d := by
  have h1 : (1 / 4 : ℝ) * b i ≤ ∑ j, (1 / 4 : ℝ) * b j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by norm_num) (hb0 j)) (Finset.mem_univ i)
  have h2 := weighted_price_le_objective v (fun _ => 1 / 4) b hz
  have h3 := balanced_price_is_minimizer v (fun _ => 1 / 4) b hv hb 0
  have h4 := expectedScore_score_le v 0 0
  rw [expectedScore_zero_zero, sub_zero, zero_add] at h4
  simp only [priceObjective, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h2 h3
  nlinarith

end GaussianFourGlobal