import GaussianOneCell

/-! The measurable-set interface: no fractional relaxation is substituted for
an original Gaussian set or its actual Bochner first moment. -/
open MeasureTheory ProbabilityTheory Set

namespace GaussianMeasureBridge

/-- The exact indicator partition associated with a measurable set and its complement. -/
noncomputable def twoCellPartition {d : ℕ} (A : Set (Space d)) (hA : MeasurableSet A) :
    FractionalPartition d 2 where
  labels i x := if i = 0 then A.indicator (fun _ => 1) x else Aᶜ.indicator (fun _ => 1) x
  measurable_labels := by
    intro i
    by_cases hi : i = 0
    · simpa only [hi, if_true] using (measurable_const.indicator hA :
        Measurable (A.indicator (fun _ : Space d => (1 : ℝ))))
    · simpa only [hi, if_false] using (measurable_const.indicator hA.compl :
        Measurable (Aᶜ.indicator (fun _ : Space d => (1 : ℝ))))
  nonneg := by
    intro i
    filter_upwards [] with x
    by_cases hi : i = 0 <;> by_cases hx : x ∈ A <;> simp [hi, hx]
  le_one := by
    intro i
    filter_upwards [] with x
    by_cases hi : i = 0 <;> by_cases hx : x ∈ A <;> simp [hi, hx]
  sum_one := by
    filter_upwards [] with x
    by_cases hx : x ∈ A <;> simp [Fin.sum_univ_two, hx]

lemma twoCellPartition_mass {d : ℕ} (A : Set (Space d)) (hA : MeasurableSet A) :
    (twoCellPartition A hA).mass 0 = ((gaussian d) A).toReal := by
  change (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂gaussian d) = _
  rw [integral_indicator hA, integral_const]
  change (((gaussian d).restrict A) univ).toReal * 1 = ((gaussian d) A).toReal
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_one]

lemma twoCellPartition_moment {d : ℕ} (A : Set (Space d)) (hA : MeasurableSet A) :
    (twoCellPartition A hA).moment 0 = ∫ x in A, x ∂gaussian d := by
  change (∫ x, (A.indicator (fun _ => (1 : ℝ)) x) • x ∂gaussian d) = _
  have he : (fun x : Space d => (A.indicator (fun _ => (1 : ℝ)) x) • x) =
      A.indicator (fun x => x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [he, integral_indicator hA]

/-- Sharp Gaussian first-moment profile for an arbitrary actual measurable set. -/
theorem measurable_set_moment_bound {d : ℕ} (A : Set (Space d)) (hA : MeasurableSet A)
    (hp : 0 < ((gaussian d) A).toReal) (hp1 : ((gaussian d) A).toReal < 1) :
    ‖∫ x in A, x ∂gaussian d‖ ≤
      standardDensity (upperQuantile (((gaussian d) A).toReal)) := by
  have hmass := twoCellPartition_mass A hA
  have h := (twoCellPartition A hA).one_cell_profile_bound 0
    (by simpa only [hmass] using hp) (by simpa only [hmass] using hp1)
  simpa only [hmass, twoCellPartition_moment] using h

/-- The upper bound for any finite family of actual measurable Gaussian sets.
It therefore applies in particular to every measurable Gaussian partition. -/
theorem measurable_sets_moment_sq_le_profile {d k : ℕ} (A : Fin k → Set (Space d))
    (hA : ∀ i, MeasurableSet (A i))
    (hp : ∀ i, 0 < ((gaussian d) (A i)).toReal)
    (hp1 : ∀ i, ((gaussian d) (A i)).toReal < 1) :
    ∑ i, ‖∫ x in A i, x ∂gaussian d‖ ^ 2 ≤
      ∑ i, standardDensity (upperQuantile (((gaussian d) (A i)).toReal)) ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  have h := measurable_set_moment_bound (A i) (hA i) (hp i) (hp1 i)
  have hn := norm_nonneg (∫ x in A i, x ∂gaussian d)
  have hs := (standardDensity_pos (upperQuantile (((gaussian d) (A i)).toReal))).le
  nlinarith

/-- Prescribed-mass version with the original paper's measurable-set objects. -/
theorem prescribed_mass_measurable_sets_bound {d k : ℕ} (A : Fin k → Set (Space d))
    (p : Fin k → ℝ) (hA : ∀ i, MeasurableSet (A i))
    (hmass : ∀ i, ((gaussian d) (A i)).toReal = p i)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    ∑ i, ‖∫ x in A i, x ∂gaussian d‖ ^ 2 ≤
      ∑ i, standardDensity (upperQuantile (p i)) ^ 2 := by
  have h := measurable_sets_moment_sq_le_profile A hA
    (fun i => by rw [hmass i]; exact hp i)
    (fun i => by rw [hmass i]; exact hp1 i)
  simpa only [hmass] using h

end GaussianMeasureBridge
