import GaussianFractionalReduction
import GaussianWinningLimits

/-! Exact measurable-set partitions, modulo null overlaps and uncovered sets,
and their actual Bochner-moment reduction to the fractional development. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianFourGlobal
open GaussianMeasureBridge

structure SetPartition (d k : ℕ) where
  cells : Fin k → Set (Space d)
  measurable_cells : ∀ i, MeasurableSet (cells i)
  ae_unique : ∀ᵐ x ∂gaussian d, ∃! i, x ∈ cells i

namespace SetPartition
variable {d k : ℕ}

/-- A genuine measurable partition, allowing pairwise null overlaps. -/
noncomputable def ofNullOverlaps (A : Fin k → Set (Space d))
    (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂gaussian d, ∃ i, x ∈ A i)
    (hdisj : ∀ i j, i ≠ j → gaussian d (A i ∩ A j) = 0) : SetPartition d k where
  cells := A
  measurable_cells := hA
  ae_unique := by
    have hd : ∀ᵐ x ∂gaussian d, ∀ i j, i ≠ j → x ∉ A i ∩ A j := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro j
      by_cases hij : i = j
      · exact ae_of_all _ fun _ h => False.elim (h hij)
      · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hdisj i j hij)] with x hx
        exact fun _ => hx
    filter_upwards [hcover, hd] with x hx hd
    obtain ⟨r, hr⟩ := hx
    refine ⟨r, hr, ?_⟩
    intro j hj
    by_contra hjr
    exact hd r j (Ne.symm hjr) ⟨hr, hj⟩

/-- The labels are precisely the original set indicators, not a relaxation
with substituted moments or weakened mass constraints. -/
noncomputable def toFractional (C : SetPartition d k) : FractionalPartition d k where
  labels i := (C.cells i).indicator (fun _ => 1)
  measurable_labels i := measurable_const.indicator (C.measurable_cells i)
  nonneg i := ae_of_all _ fun x => by
    by_cases hx : x ∈ C.cells i <;> simp [hx]
  le_one i := ae_of_all _ fun x => by
    by_cases hx : x ∈ C.cells i <;> simp [hx]
  sum_one := by
    classical
    filter_upwards [C.ae_unique] with x hx
    obtain ⟨r, hr, hu⟩ := hx
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro j _ hj
      have hnot : x ∉ C.cells j := fun h => hj (hu j h)
      simp [hnot]
    · simp

lemma toFractional_mass (C : SetPartition d k) (i : Fin k) :
    C.toFractional.mass i = (gaussian d).real (C.cells i) := by
  simpa only [toFractional, FractionalPartition.mass, smul_eq_mul, mul_one] using
    integral_indicator_const (1 : ℝ) (C.measurable_cells i)

lemma toFractional_moment (C : SetPartition d k) (i : Fin k) :
    C.toFractional.moment i = ∫ x in C.cells i, x ∂gaussian d := by
  change (∫ x, (C.cells i).indicator (fun _ => (1 : ℝ)) x • x ∂gaussian d) = _
  rw [← integral_indicator (C.measurable_cells i)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ C.cells i <;> simp [hx]

/-- The first moments of any actual measurable Gaussian partition sum to zero. -/
theorem sum_set_moment (C : SetPartition d k) :
    ∑ i, (∫ x in C.cells i, x ∂gaussian d) = 0 := by
  simpa only [toFractional_moment] using C.toFractional.sum_moment

/-- Null modifications preserve the actual set-integral first moments. -/
theorem moment_eq_of_ae_cells (C D : SetPartition d k)
    (h : ∀ i, ∀ᵐ x ∂gaussian d, x ∈ C.cells i ↔ x ∈ D.cells i) (i : Fin k) :
    (∫ x in C.cells i, x ∂gaussian d) = ∫ x in D.cells i, x ∂gaussian d := by
  rw [← integral_indicator (C.measurable_cells i), ← integral_indicator (D.measurable_cells i)]
  apply integral_congr_ae
  filter_upwards [h i] with x hx
  by_cases hc : x ∈ C.cells i
  · simp [hc, hx.mp hc]
  · have hd : x ∉ D.cells i := fun h => hc (hx.mpr h)
    simp [hc, hd]

lemma mass_quarter (C : SetPartition d 4)
    (hm : ∀ i, gaussian d (C.cells i) = 1 / 4) (i : Fin 4) :
    C.toFractional.mass i = 1 / 4 := by
  rw [toFractional_mass, measureReal_def, hm]
  norm_num

/-- The original measurable-set objects satisfy the own-score assignment bound. -/
theorem energy_le_value (C : SetPartition d 4)
    (hm : ∀ i, gaussian d (C.cells i) = 1 / 4) :
    (∑ i, ‖∫ x in C.cells i, x ∂gaussian d‖ ^ 2) ≤
      balancedValue (fun i => ∫ x in C.cells i, x ∂gaussian d) := by
  have h := energy_le_balancedValue C.toFractional (C.mass_quarter hm)
  have he : C.toFractional.moment = (fun i => ∫ x in C.cells i, x ∂gaussian d) :=
    funext C.toFractional_moment
  simpa only [momentEnergy, he] using h

/-- Every positive-energy actual balanced set partition yields a centered,
trace-one Gaussian score list with at least the square-root energy value. -/
theorem normalized_reduction (C : SetPartition d 4)
    (hm : ∀ i, gaussian d (C.cells i) = 1 / 4)
    (hE : 0 < ∑ i, ‖∫ x in C.cells i, x ∂gaussian d‖ ^ 2) :
    ∃ v : Fin 4 → Space d, (∑ i, v i = 0) ∧ (∑ i, ‖v i‖ ^ 2 = 1) ∧
      Real.sqrt (∑ i, ‖∫ x in C.cells i, x ∂gaussian d‖ ^ 2) ≤ balancedValue v := by
  have he : C.toFractional.moment = (fun i => ∫ x in C.cells i, x ∂gaussian d) :=
    funext C.toFractional_moment
  have hEF : 0 < momentEnergy C.toFractional := by
    simpa only [momentEnergy, he] using hE
  refine ⟨normalizedMoments C.toFractional, sum_normalizedMoments C.toFractional,
    normalizedMoments_energy_one C.toFractional hEF, ?_⟩
  simpa only [momentEnergy, toFractional_moment] using
    sqrt_energy_le_normalized_value C.toFractional (C.mass_quarter hm) hEF

end SetPartition
end GaussianFourGlobal