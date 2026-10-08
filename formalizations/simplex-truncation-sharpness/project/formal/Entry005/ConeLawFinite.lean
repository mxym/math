import Entry005.UnitBallAnchorChain
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
Finite cone-law cancellation, independently of surface-area geometry.
The weights are exactly `aᵢ hᵢ / M` and the atoms exactly `nᵢ / hᵢ`.
This module does not assert that arbitrary input arrays are facets of a body.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

section FiniteLaw

variable {ι : Type*} [Fintype ι] {d : ℕ}

def finiteConePoint (n : ι → Fin d → ℝ) (h : ι → ℝ) (i : ι) : Fin d → ℝ :=
  fun j => n i j / h i

def finiteConeLaw (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ) :
    Measure (Fin d → ℝ) :=
  Measure.sum fun i => ENNReal.ofReal (a i * h i / M) •
    Measure.dirac (finiteConePoint n h i)

theorem finite_cone_integrable (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (f : (Fin d → ℝ) → ℝ) : Integrable f (finiteConeLaw a h n M) := by
  apply integrable_sum_dirac
  · intro i; exact ENNReal.ofReal_ne_top
  · exact (hasSum_fintype _).summable

theorem finite_cone_integral (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ x, f x ∂finiteConeLaw a h n M) =
      ∑ i, (a i * h i / M) * f (finiteConePoint n h i) := by
  rw [finiteConeLaw, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (ha i) (hh i).le) hM.le)]
  rfl

theorem finite_cone_probability (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hmass : ∑ i, a i * h i = M) : IsProbabilityMeasure (finiteConeLaw a h n M) := by
  constructor
  simp only [finiteConeLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      div_nonneg (mul_nonneg (ha i) (hh i).le) hM.le), ← Finset.sum_div,
    hmass, div_self hM.ne', ENNReal.ofReal_one]

theorem finite_cone_coordinate_mean (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M) (j : Fin d) :
    (∫ x, x j ∂finiteConeLaw a h n M) = (∑ i, a i * n i j) / M := by
  rw [finite_cone_integral a h n M ha hh hM, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [finiteConePoint]
  field_simp [(hh i).ne']

theorem finite_cone_centered (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hbalance : ∀ j, ∑ i, a i * n i j = 0) :
    ∀ j, (∫ x, x j ∂finiteConeLaw a h n M) = 0 := by
  intro j
  rw [finite_cone_coordinate_mean a h n M ha hh hM, hbalance j, zero_div]

omit [Fintype ι] in
theorem finite_cone_point_norm (n : ι → Fin d → ℝ) (h : ι → ℝ)
    (hh : ∀ i, 0 < h i) (hn : ∀ i, ‖WithLp.toLp 2 (n i)‖ ≤ h i) (i : ι) :
    ‖WithLp.toLp 2 (finiteConePoint n h i)‖ ≤ 1 := by
  have heq : WithLp.toLp 2 (finiteConePoint n h i) =
      (h i)⁻¹ • WithLp.toLp 2 (n i) := by
    ext j
    simp [finiteConePoint, div_eq_mul_inv, mul_comm]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hh i))]
  exact (inv_mul_le_iff₀ (hh i)).mpr (by simpa using hn i)

theorem finite_cone_ae_unit_ball (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (hh : ∀ i, 0 < h i) (hn : ∀ i, ‖WithLp.toLp 2 (n i)‖ ≤ h i) :
    ∀ᵐ x ∂finiteConeLaw a h n M, ‖WithLp.toLp 2 x‖ ≤ 1 := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff ((isClosed_le
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm continuous_const).measurableSet)).mpr
      (finite_cone_point_norm n h hh hn i)

theorem finite_cone_support_unit_ball (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (hh : ∀ i, 0 < h i) (hn : ∀ i, ‖WithLp.toLp 2 (n i)‖ ≤ h i) :
    ∀ x ∈ (finiteConeLaw a h n M).support, ‖WithLp.toLp 2 x‖ ≤ 1 :=
  unit_ball_support_bound _ (finite_cone_ae_unit_ball a h n M hh hn)

theorem finite_cone_absolute_direction (a h : ι → ℝ) (n : ι → Fin d → ℝ)
    (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (u : Fin d → ℝ) :
    (∫ x, |dotProduct u x| ∂finiteConeLaw a h n M) =
      (∑ i, a i * |dotProduct u (n i)|) / M := by
  rw [finite_cone_integral a h n M ha hh hM, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hd : dotProduct u (finiteConePoint n h i) = dotProduct u (n i) / h i := by
    simp [dotProduct, finiteConePoint, mul_div_assoc, Finset.sum_div]
  rw [hd, abs_div, abs_of_pos (hh i)]
  field_simp [(hh i).ne']

theorem finite_cone_direction_mean_zero (a h : ι → ℝ) (n : ι → Fin d → ℝ)
    (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hbalance : ∀ j, ∑ i, a i * n i j = 0) (u : Fin d → ℝ) :
    (∫ x, dotProduct u x ∂finiteConeLaw a h n M) = 0 := by
  rw [show (fun x => dotProduct u x) =
    (fun x => ∑ j, u j * x j) from rfl]
  rw [integral_finsetSum _ (fun j _ =>
    (finite_cone_integrable a h n M (fun x => x j)).const_mul _)]
  simp [integral_const_mul, finite_cone_centered a h n M ha hh hM hbalance]

theorem finite_cone_negative_direction (a h : ι → ℝ) (n : ι → Fin d → ℝ)
    (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hbalance : ∀ j, ∑ i, a i * n i j = 0) (u : Fin d → ℝ) :
    negativeIntegral (finiteConeLaw a h n M) (fun x => dotProduct u x) =
      (∑ i, a i * |dotProduct u (n i)|) / (2 * M) := by
  have hf := finite_cone_integrable a h n M (fun x => dotProduct u x)
  have hm := integral_mean_decomposition hf
  have habs := integral_absolute_decomposition hf
  rw [finite_cone_direction_mean_zero a h n M ha hh hM hbalance] at hm
  rw [finite_cone_absolute_direction a h n M ha hh hM] at habs
  have hd : (∑ i, a i * |dotProduct u (n i)|) / (2 * M) =
      ((∑ i, a i * |dotProduct u (n i)|) / M) / 2 := by ring
  rw [hd]
  linarith

section IndexLaw

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finiteConeIndexLaw (a h : ι → ℝ) (M : ℝ) : Measure ι :=
  Measure.sum fun i => ENNReal.ofReal (a i * h i / M) • Measure.dirac i

omit [MeasurableSingletonClass ι] in
theorem finite_cone_index_probability (a h : ι → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hmass : ∑ i, a i * h i = M) : IsProbabilityMeasure (finiteConeIndexLaw a h M) := by
  constructor
  simp only [finiteConeIndexLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      div_nonneg (mul_nonneg (ha i) (hh i).le) hM.le), ← Finset.sum_div,
    hmass, div_self hM.ne', ENNReal.ofReal_one]

theorem finite_cone_index_map (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ) :
    (finiteConeIndexLaw a h M).map (finiteConePoint n h) = finiteConeLaw a h n M := by
  rw [finiteConeIndexLaw, Measure.map_sum (measurable_of_finite _).aemeasurable]
  simp_rw [Measure.map_smul _ (measurable_of_finite _).aemeasurable, Measure.map_dirac]
  rfl

theorem finite_cone_index_singleton (a h : ι → ℝ) (M : ℝ) (i : ι) :
    (finiteConeIndexLaw a h M) {i} = ENNReal.ofReal (a i * h i / M) := by
  classical
  simp [finiteConeIndexLaw, Pi.single_apply, mul_ite]

theorem finite_cone_iid_integral (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hmass : ∑ i, a i * h i = M) (k : ℕ)
    (f : (Fin k → Fin d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ w, f w ∂iidLaw (finiteConeLaw a h n M) k) =
      ∑ b : Fin k → ι, (∏ j, (a (b j) * h (b j) / M)) *
        f (fun j => finiteConePoint n h (b j)) := by
  let μ := finiteConeIndexLaw a h M
  have : IsProbabilityMeasure μ := finite_cone_index_probability a h M ha hh hM hmass
  have : IsProbabilityMeasure (finiteConeLaw a h n M) :=
    finite_cone_probability a h n M ha hh hM hmass
  have hmap : (iidLaw μ k).map (fun b j => finiteConePoint n h (b j)) =
      iidLaw (finiteConeLaw a h n M) k := by
    simpa only [μ, iidLaw, finite_cone_index_map] using
      (Measure.pi_map_pi (μ := fun _ : Fin k => μ)
        (fun _ => (measurable_of_finite (finiteConePoint n h)).aemeasurable))
  rw [← hmap, integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Measure.real, iidLaw, Measure.pi_singleton, μ,
    finite_cone_index_singleton, ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (ha (b j)) (hh (b j)).le) hM.le)

end IndexLaw

omit [Fintype ι] in
theorem finite_cone_weighted_sample_determinant {k : ℕ}
    (a h : ι → ℝ) (v : ι → Fin k → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (b : Fin k → ι) :
    (∏ j, a (b j) * h (b j) / M) *
        |(sampledMatrix (finiteConePoint v h) b).det| =
      |(sampledMatrix (fun i j => a i * v i j) b).det| / M ^ k := by
  have hpoint : (sampledMatrix (finiteConePoint v h) b).det =
      (∏ j, (h (b j))⁻¹) * (sampledMatrix v b).det := by
    convert Matrix.det_mul_row (fun j => (h (b j))⁻¹) (sampledMatrix v b) using 1
    congr 1
    ext i j
    simp [sampledMatrix, finiteConePoint, div_eq_mul_inv, mul_comm]
  have harea : (sampledMatrix (fun i j => a i * v i j) b).det =
      (∏ j, a (b j)) * (sampledMatrix v b).det :=
    Matrix.det_mul_row (fun j => a (b j)) (sampledMatrix v b)
  have hhprod : 0 < ∏ j : Fin k, h (b j) := Finset.prod_pos (fun j _ => hh (b j))
  have haprod : 0 ≤ ∏ j : Fin k, a (b j) := Finset.prod_nonneg (fun j _ => ha (b j))
  rw [hpoint, harea, abs_mul, abs_mul, abs_of_nonneg haprod,
    Finset.prod_inv_distrib, abs_of_pos (inv_pos.mpr hhprod),
    Finset.prod_div_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hhprod.ne']

section DeterminantExpectations

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finite_cone_horizontal_determinant_expectation (a h : ι → ℝ)
    (n : ι → Fin d → ℝ) (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i)
    (hM : 0 < M) (hmass : ∑ i, a i * h i = M) :
    (∫ w, |horizontalDeterminant w| ∂iidLaw (finiteConeLaw a h n M) d) =
      (∑ b : Fin d → ι,
        |horizontalDeterminant (fun j l => a (b j) * n (b j) l)|) / M ^ d := by
  have hdet : Measurable (fun w : Fin d → Fin d → ℝ => horizontalDeterminant w) := by
    unfold horizontalDeterminant
    simp only [Matrix.det_apply]
    apply Finset.measurable_sum
    intro p _
    apply Measurable.const_smul
    apply Finset.measurable_prod
    intro i _
    exact (measurable_pi_apply (p i)).comp (measurable_pi_apply i)
  rw [finite_cone_iid_integral a h n M ha hh hM hmass d _
    (by simpa only [Real.norm_eq_abs] using hdet.norm)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  exact finite_cone_weighted_sample_determinant a h n M ha hh b

def finiteFacetLift (h : ι → ℝ) (n : ι → Fin d → ℝ) (i : ι) : Fin (d + 1) → ℝ :=
  Fin.cases (h i) (n i)

theorem finite_cone_lifted_determinant_expectation (a h : ι → ℝ)
    (n : ι → Fin d → ℝ) (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i)
    (hM : 0 < M) (hmass : ∑ i, a i * h i = M) :
    (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (finiteConeLaw a h n M) (d + 1)) =
      (∑ b : Fin (d + 1) → ι,
        |(sampledMatrix (fun i j => a i * finiteFacetLift h n i j) b).det|) /
          M ^ (d + 1) := by
  have hdet : Measurable (fun w : Fin (d + 1) → Fin d → ℝ =>
      liftedDeterminant (fun j => w j.succ) (w 0)) :=
    measurable_lifted_determinant
      (fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i.succ))
      (fun j => (measurable_pi_apply j).comp (measurable_pi_apply 0))
  rw [finite_cone_iid_integral a h n M ha hh hM hmass (d + 1) _
      (by simpa only [Real.norm_eq_abs] using hdet.norm),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  have heq : witnessMatrix
      (fun j => finiteConePoint n h (b j.succ)) (finiteConePoint n h (b 0)) =
      sampledMatrix (finiteConePoint (finiteFacetLift h n) h) b := by
    ext i j
    induction j using Fin.cases with
    | zero =>
      induction i using Fin.cases <;>
        simp [witnessMatrix, sampledMatrix, finiteConePoint, finiteFacetLift, (hh (b 0)).ne']
    | succ j =>
      induction i using Fin.cases <;>
        simp [witnessMatrix, sampledMatrix, finiteConePoint, finiteFacetLift, (hh (b j.succ)).ne']
  rw [liftedDeterminant, heq]
  exact finite_cone_weighted_sample_determinant a h (finiteFacetLift h n) M ha hh b

end DeterminantExpectations

end FiniteLaw
end Entry005
