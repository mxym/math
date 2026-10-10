import GaussianBalancedValue

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

lemma scoreMax_smul (v : Fin k → Space d) (b : Fin k → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (x : Space d) : scoreMax (a • v) (a • b) x = a * scoreMax v b x := by
  classical
  apply le_antisymm
  · unfold scoreMax
    refine Finset.sup'_le _ _ fun i _ => ?_
    change ⟪a • v i, x⟫ - a * b i ≤ a * scoreMax v b x
    rw [real_inner_smul_left, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_scoreMax v b x i) ha
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin k => ⟪v i, x⟫ - b i)
    change scoreMax v b x = ⟪v i, x⟫ - b i at hi
    rw [hi, mul_sub]
    simpa only [Pi.smul_apply, real_inner_smul_left, smul_eq_mul] using
      le_scoreMax (a • v) (a • b) x i

lemma priceObjective_smul (v : Fin k → Space d) (p b : Fin k → ℝ)
    (a : ℝ) (ha : 0 ≤ a) :
    priceObjective (a • v) p (a • b) = a * priceObjective v p b := by
  unfold priceObjective expectedScore
  simp_rw [scoreMax_smul v b a ha, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma scoreMax_zero_zero (x : Space d) :
    scoreMax (0 : Fin k → Space d) 0 x = 0 := by
  classical
  simp [scoreMax]

lemma balancedValue_zero (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    balancedValue (0 : Fin k → Space d) p = 0 := by
  apply le_antisymm _ (balancedValue_nonneg _ p hp hs)
  have h := balancedValue_le_objective (0 : Fin k → Space d) p 0 hp hs
  simpa [priceObjective, expectedScore, scoreMax_zero_zero] using h

/-- Positive and zero score scaling, proved for the integral-defined value. -/
theorem balancedValue_smul (v : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (a : ℝ) (ha : 0 ≤ a) :
    balancedValue (a • v) p = a * balancedValue v p := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [balancedValue_zero p hp hs]
  obtain ⟨b, hb, _⟩ := balancedValue_attained v p hp hs
  obtain ⟨c, hc, _⟩ := balancedValue_attained (a • v) p hp hs
  apply le_antisymm
  · calc
      balancedValue (a • v) p ≤ priceObjective (a • v) p (a • b) :=
        balancedValue_le_objective _ p _ hp hs
      _ = a * balancedValue v p := by rw [priceObjective_smul v p b a ha.le, hb]
  · have h := mul_le_mul_of_nonneg_left
      (balancedValue_le_objective v p (a⁻¹ • c) hp hs) ha.le
    rw [← priceObjective_smul v p (a⁻¹ • c) a ha.le, smul_smul,
      mul_inv_cancel₀ ha.ne', one_smul, ← hc] at h
    exact h

/-- The constant mass function used in the all-label theorem. -/
noncomputable def uniformMass (k : ℕ) : Fin k → ℝ := fun _ => (k : ℝ)⁻¹

lemma uniformMass_pos (i : Fin k) : 0 < uniformMass k i := by
  unfold uniformMass
  exact inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos k))

lemma sum_uniformMass : ∑ i : Fin k, uniformMass k i = 1 := by
  classical
  simp [uniformMass, ne_of_gt (Nat.cast_pos.mpr (NeZero.pos k) : (0 : ℝ) < k)]

noncomputable def equalMassValue (v : Fin k → Space d) : ℝ :=
  balancedValue v (uniformMass k)

theorem continuous_equalMassValue : Continuous (equalMassValue (d := d) (k := k)) :=
  continuous_balancedValue _ uniformMass_pos sum_uniformMass

theorem equalMassValue_smul (v : Fin k → Space d) (a : ℝ) (ha : 0 ≤ a) :
    equalMassValue (a • v) = a * equalMassValue v :=
  balancedValue_smul v _ uniformMass_pos sum_uniformMass a ha

namespace FractionalPartition

noncomputable def momentEnergy (F : FractionalPartition d k) : ℝ :=
  ∑ i, ‖F.moment i‖ ^ 2

lemma momentEnergy_nonneg (F : FractionalPartition d k) : 0 ≤ F.momentEnergy :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The actual moment energy is dominated by the actual equal-mass score value,
including the zero-energy and coincident-moment cases. -/
theorem momentEnergy_le_equalMassValue (F : FractionalPartition d k)
    (hF : ∀ i, F.mass i = uniformMass k i) :
    F.momentEnergy ≤ equalMassValue F.moment := by
  have h := partitionValue_le_balancedValue F.moment (uniformMass k)
    uniformMass_pos sum_uniformMass F hF
  simpa only [partitionValue, equalMassValue, momentEnergy, real_inner_self_eq_norm_sq] using h

/-- Once a bound on the actual moment score has been established, the final
quadratic step needs only the nonnegativity of the proposed sharp constant. -/
theorem momentEnergy_le_sq_of_score_bound (F : FractionalPartition d k)
    (hF : ∀ i, F.mass i = uniformMass k i) (c : ℝ) (_hc : 0 ≤ c)
    (hscore : equalMassValue F.moment ≤ c * Real.sqrt F.momentEnergy) :
    F.momentEnergy ≤ c ^ 2 := by
  have h := (F.momentEnergy_le_equalMassValue hF).trans hscore
  have hF0 := F.momentEnergy_nonneg
  have hsqrt := Real.sq_sqrt hF0
  have hsqrt0 := Real.sqrt_nonneg F.momentEnergy
  nlinarith [sq_nonneg (Real.sqrt F.momentEnergy - c)]

end FractionalPartition
end GaussianMeasureBridge
