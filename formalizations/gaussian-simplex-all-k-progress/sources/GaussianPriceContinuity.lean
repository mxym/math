import GaussianScoreSymmetry
import Mathlib.Topology.Bases

/-! Continuous normalized minimizing prices for the actual Gaussian objective.
This uses compactness, coercivity and the proved uniqueness theorem; no facet
Hessian or implicit-function theorem is assumed. -/
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma expectedScore_score_lipschitz (b : Fin k → ℝ) :
    LipschitzWith ⟨gaussianMeanNorm d, gaussianMeanNorm_nonneg d⟩
      (fun v : Fin k → Space d => expectedScore v b) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  have h₁ := priceObjective_le_add_score_norm v w (0 : Fin k → ℝ) b
  have h₂ := priceObjective_le_add_score_norm w v (0 : Fin k → ℝ) b
  simp only [priceObjective, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h₁ h₂
  rw [norm_sub_rev w v] at h₂
  change |expectedScore v b - expectedScore w b| ≤ gaussianMeanNorm d * ‖v-w‖
  rw [mul_comm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma continuous_joint_priceObjective (p : Fin k → ℝ) :
    Continuous (fun z : (Fin k → Space d) × (Fin k → ℝ) => priceObjective z.1 p z.2) := by
  have h : Continuous (fun z : (Fin k → Space d) × (Fin k → ℝ) => expectedScore z.1 z.2) :=
    continuous_prod_of_continuous_lipschitzWith _
      ⟨gaussianMeanNorm d, gaussianMeanNorm_nonneg d⟩
      (fun v => (expectedScore_lipschitz v).continuous)
      (fun b => expectedScore_score_lipschitz b)
  exact h.add (continuous_finsetSum _ fun i _ => by fun_prop)

def firstLabel (k : ℕ) [NeZero k] : Fin k := ⟨0, NeZero.pos k⟩

lemma exists_normalized_minimizer (v : Fin k → Space d) : ∃ b : Fin k → ℝ,
    (∀ c, priceObjective v (uniformMass k) b ≤ priceObjective v (uniformMass k) c) ∧
    b (firstLabel k) = 0 := by
  obtain ⟨b,hb⟩ := exists_price_minimizer v (uniformMass k) uniformMass_pos sum_uniformMass
  refine ⟨fun i => b i - b (firstLabel k), ?_, sub_self _⟩
  intro c
  rw [priceObjective_sub_const _ _ _ sum_uniformMass]
  exact hb c

noncomputable def canonicalPrices (v : Fin k → Space d) : Fin k → ℝ :=
  Classical.choose (exists_normalized_minimizer v)

lemma canonicalPrices_min (v : Fin k → Space d) (c : Fin k → ℝ) :
    priceObjective v (uniformMass k) (canonicalPrices v) ≤ priceObjective v (uniformMass k) c :=
  (Classical.choose_spec (exists_normalized_minimizer v)).1 c

@[simp] lemma canonicalPrices_first (v : Fin k → Space d) :
    canonicalPrices v (firstLabel k) = 0 :=
  (Classical.choose_spec (exists_normalized_minimizer v)).2

lemma canonicalPrices_value (v : Fin k → Space d) :
    priceObjective v (uniformMass k) (canonicalPrices v) = equalMassValue v :=
  (balancedValue_eq_of_minimizer _ _ _ (canonicalPrices_min v)).symm

lemma minimizing_prices_balanced (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hv : Function.Injective v) (hb : ∀ c, priceObjective v p b ≤ priceObjective v p c) :
    ∀ i, (gaussian d).real (winningCell v b i) = p i := by
  intro i
  have hlocal : IsLocalMin (fun t => priceObjective v p (coordinateShift b i t)) 0 :=
    Eventually.of_forall fun t => by simpa only [coordinateShift_zero] using hb (coordinateShift b i t)
  have hz := hlocal.hasDerivAt_eq_zero (priceObjective_coordinate_derivative v p b hv i)
  linarith

lemma canonicalPrices_balanced (v : Fin k → Space d) (hv : Function.Injective v) :
    ∀ i, (gaussian d).real (winningCell v (canonicalPrices v) i) = uniformMass k i :=
  minimizing_prices_balanced v _ _ hv (canonicalPrices_min v)

lemma canonicalPrices_unique (v : Fin k → Space d) (hv : Function.Injective v)
    (b : Fin k → ℝ) (hb : ∀ c, priceObjective v (uniformMass k) b ≤ priceObjective v (uniformMass k) c)
    (hb0 : b (firstLabel k) = 0) : b = canonicalPrices v := by
  obtain ⟨a, ha⟩ := minimizing_prices_eq_balancing_mod_const v (uniformMass k)
    (canonicalPrices v) b hv uniformMass_pos (canonicalPrices_balanced v hv) hb
  have hz := ha (firstLabel k)
  rw [hb0, canonicalPrices_first] at hz
  have ha0 : a = 0 := by linarith
  ext i
  simpa [ha0] using ha i

/-- Quantitative coercivity of the normalized actual optimal prices. -/
lemma canonicalPrices_norm_le (v : Fin k → Space d) :
    ‖canonicalPrices v‖ ≤ (k : ℝ) * equalMassValue v := by
  classical
  let b := canonicalPrices v
  obtain ⟨r, hr⟩ := Finite.exists_min b
  let c : Fin k → ℝ := fun i => b i - b r
  have hc : ∀ i, 0 ≤ c i := fun i => sub_nonneg.mpr (hr i)
  have hval : priceObjective v (uniformMass k) c = equalMassValue v := by
    rw [show c = (fun i => b i - b r) from rfl,
      priceObjective_sub_const _ _ _ sum_uniformMass]
    exact canonicalPrices_value v
  have hw := weighted_price_le_objective v (uniformMass k) c ⟨r, sub_self _⟩
  rw [hval] at hw
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hci : ∀ i, c i ≤ (k : ℝ) * equalMassValue v := by
    intro i
    have hh : (k : ℝ)⁻¹ * c i ≤ equalMassValue v :=
      (Finset.single_le_sum (fun j _ => mul_nonneg (uniformMass_pos j).le (hc j))
        (Finset.mem_univ i)).trans hw
    have hh' := mul_le_mul_of_nonneg_left hh hk.le
    rwa [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] at hh'
  have hb0 : b (firstLabel k) = 0 := canonicalPrices_first v
  have hmin : b r ≤ 0 := by simpa only [hb0] using hr (firstLabel k)
  have hlow := hci (firstLabel k)
  dsimp [c] at hlow
  rw [hb0] at hlow
  have hnonneg : 0 ≤ (k : ℝ) * equalMassValue v := mul_nonneg hk.le
    (balancedValue_nonneg v (uniformMass k) uniformMass_pos sum_uniformMass)
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro i
  have hi := hci i
  have hlo := hr i
  change ‖b i‖ ≤ _
  rw [Real.norm_eq_abs]
  dsimp [c] at hi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual normalized price minimizer is continuous at every distinct
score family, including families whose covariance has lower rank. -/
theorem continuousAt_canonicalPrices (v : Fin k → Space d) (hv : Function.Injective v) :
    ContinuousAt canonicalPrices v := by
  let C : ℝ := (k : ℝ) * (equalMassValue v + 1)
  have hC : 0 ≤ C := by
    have h := balancedValue_nonneg v (uniformMass k) uniformMass_pos sum_uniformMass
    dsimp [C]; positivity
  let S : Set (Fin k → ℝ) := closedBall 0 C
  apply (isCompact_closedBall (0 : Fin k → ℝ) C).tendsto_nhds_of_unique_mapClusterPt
  · have he : ∀ᶠ w in 𝓝 v, equalMassValue w < equalMassValue v + 1 :=
      continuous_equalMassValue.continuousAt.eventually_lt continuousAt_const (by linarith)
    filter_upwards [he] with w hw
    rw [mem_closedBall_zero_iff]
    exact (canonicalPrices_norm_le w).trans (mul_le_mul_of_nonneg_left hw.le (Nat.cast_nonneg k))
  · intro b _ hcluster
    obtain ⟨u, hbu, hu⟩ := hcluster.exists_seq_tendsto
    have hvu := continuous_equalMassValue.continuousAt.tendsto.comp hu
    have hobj := (continuous_joint_priceObjective (uniformMass k)).continuousAt.tendsto.comp
      (hu.prodMk_nhds hbu)
    have heq : priceObjective v (uniformMass k) b = equalMassValue v := by
      apply tendsto_nhds_unique hobj
      convert hvu using 1
      funext n
      exact canonicalPrices_value (u n)
    have hb0 : b (firstLabel k) = 0 := by
      have he := (continuous_apply (firstLabel k)).continuousAt.tendsto.comp hbu
      have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (b (firstLabel k))) := by
        change Tendsto (fun n => canonicalPrices (u n) (firstLabel k)) atTop
          (𝓝 (b (firstLabel k))) at he
        simpa only [canonicalPrices_first] using he
      exact (tendsto_nhds_unique hz tendsto_const_nhds)
    apply canonicalPrices_unique v hv b _ hb0
    intro c
    rw [heq]
    exact balancedValue_le_objective v (uniformMass k) c uniformMass_pos sum_uniformMass

end GaussianMeasureBridge
