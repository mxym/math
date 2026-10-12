import GaussianHomogeneity

/-! Reduction of arbitrary balanced fractional partitions to centered,
trace-one actual Gaussian score lists. This is not the missing sharp
comparison for those score lists or a tetrahedral equality classification. -/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace GaussianFourGlobal
open GaussianMeasureBridge

noncomputable def momentEnergy {d : ℕ} (F : FractionalPartition d 4) : ℝ :=
  ∑ i, ‖F.moment i‖ ^ 2

lemma momentEnergy_nonneg {d : ℕ} (F : FractionalPartition d 4) : 0 ≤ momentEnergy F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma uniformPartition_energy (d : ℕ) : momentEnergy (uniformPartition d) = 0 := by
  simp [momentEnergy, uniformPartition_moment]

lemma self_partitionValue {d : ℕ} (F : FractionalPartition d 4) :
    partitionValue F.moment F = momentEnergy F := by
  simp only [partitionValue, momentEnergy, real_inner_self_eq_norm_sq]

/-- The actual first-moment energy is bounded by its own-score assignment value. -/
theorem energy_le_balancedValue {d : ℕ} (F : FractionalPartition d 4)
    (hm : ∀ i, F.mass i = 1 / 4) : momentEnergy F ≤ balancedValue F.moment := by
  rw [← self_partitionValue]
  exact fractional_value_le_balancedValue F hm F.moment

noncomputable def normalizedMoments {d : ℕ} (F : FractionalPartition d 4) : Fin 4 → Space d :=
  fun i => (Real.sqrt (momentEnergy F))⁻¹ • F.moment i

/-- Centering uses the actual zero Gaussian mean, not a synthetic moment constraint. -/
theorem sum_normalizedMoments {d : ℕ} (F : FractionalPartition d 4) :
    ∑ i, normalizedMoments F i = 0 := by
  simp only [normalizedMoments, ← Finset.smul_sum, F.sum_moment, smul_zero]

/-- Positive-energy normalized moment scores have exactly unit squared norm sum. -/
theorem normalizedMoments_energy_one {d : ℕ} (F : FractionalPartition d 4)
    (hE : 0 < momentEnergy F) : ∑ i, ‖normalizedMoments F i‖ ^ 2 = 1 := by
  have hs : Real.sqrt (momentEnergy F) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hE)
  simp only [normalizedMoments, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg (momentEnergy F)), mul_pow]
  rw [← Finset.mul_sum]
  change (Real.sqrt (momentEnergy F))⁻¹ ^ 2 * momentEnergy F = 1
  field_simp [hs]
  exact (Real.sq_sqrt hE.le).symm

lemma normalized_partitionValue {d : ℕ} (F : FractionalPartition d 4)
    (hE : 0 < momentEnergy F) :
    partitionValue (normalizedMoments F) F = Real.sqrt (momentEnergy F) := by
  have hs : Real.sqrt (momentEnergy F) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hE)
  simp only [partitionValue, normalizedMoments, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  rw [← Finset.mul_sum]
  change (Real.sqrt (momentEnergy F))⁻¹ * momentEnergy F = Real.sqrt (momentEnergy F)
  field_simp [hs]
  exact (Real.sq_sqrt hE.le).symm

/-- The normalized feasible-assignment inequality for every actual balanced
fractional partition with positive first-moment energy. -/
theorem sqrt_energy_le_normalized_value {d : ℕ} (F : FractionalPartition d 4)
    (hm : ∀ i, F.mass i = 1 / 4) (hE : 0 < momentEnergy F) :
    Real.sqrt (momentEnergy F) ≤ balancedValue (normalizedMoments F) := by
  have h := fractional_value_le_balancedValue F hm (normalizedMoments F)
  rwa [normalized_partitionValue F hE] at h

/-- Equality in the own-score assignment inequality forces actual winning
labels. This is a self-moment statement, not yet geometric tetrahedral rigidity. -/
theorem winning_labels_of_energy_value_equality {d : ℕ} (F : FractionalPartition d 4)
    (hm : ∀ i, F.mass i = 1 / 4) (hv : Function.Injective F.moment)
    (hEq : momentEnergy F = balancedValue F.moment) :
    ∃ b : Fin 4 → ℝ,
      (∀ i, (gaussian d).real (winningCell F.moment b i) = 1 / 4) ∧
      (∀ᵐ x ∂gaussian d, ∀ i, F.labels i x = (winningPartition F.moment b hv).labels i x) := by
  obtain ⟨b, hb⟩ := exists_balancing_prices F.moment (fun _ => 1 / 4) hv
    (fun _ => by norm_num) (by norm_num)
  have hmin := balanced_price_is_minimizer F.moment (fun _ => 1 / 4) b hv hb
  have hval := balancedValue_eq_minimizer F.moment b hmin
  refine ⟨b, hb, fractional_dual_equality_ae_winning F.moment b hv F ?_⟩
  simp only [hm]
  rw [self_partitionValue, hEq, hval]

end GaussianFourGlobal