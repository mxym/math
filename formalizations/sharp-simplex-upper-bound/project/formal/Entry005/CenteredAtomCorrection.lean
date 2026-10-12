import Entry005.SelectedAnchorHullRoundness
import Entry005.FiniteLawZonotopeMoment
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Metric
open scoped BigOperators RealInnerProductSpace

namespace Entry005

theorem finite_convex_hull_probability_weights
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (w : ι → E) (y : E) (hy : y ∈ convexHull ℝ (Set.range w)) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∑ i, q i • w i = y := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, q, hq, hsum, hmean⟩ := hy
  refine ⟨fun i => if i ∈ s then q i else 0, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hq i hi
    · exact le_refl 0
  · simpa only [Finset.sum_ite_mem_eq] using hsum
  · simp_rw [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem_eq]
    rwa [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hmean

def centeredAtomMixture {ι : Type*} (p q : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => (p i + t * q i) / (1 + t)

theorem centered_atom_mixture_probability {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (t : ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) (ht : 0 ≤ t) :
    (∀ i, 0 ≤ centeredAtomMixture p q t i) ∧ ∑ i, centeredAtomMixture p q t i = 1 := by
  refine ⟨fun i => div_nonneg (add_nonneg (hp i) (mul_nonneg ht (hq i))) (by positivity), ?_⟩
  simp only [centeredAtomMixture, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, hpsum, hqsum, mul_one]
  exact div_self (by positivity)

theorem centered_atom_mixture_mean {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (w : ι → E) (p q : ι → ℝ) (t : ℝ) :
    ∑ i, centeredAtomMixture p q t i • w i =
      (1 + t)⁻¹ • ((∑ i, p i • w i) + t • ∑ i, q i • w i) := by
  have hp (i : ι) : centeredAtomMixture p q t i • w i =
      (1 + t)⁻¹ • (p i • w i + t • (q i • w i)) := by
    simp only [centeredAtomMixture, div_eq_mul_inv, add_mul, add_smul, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp_rw [hp]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum]

theorem finite_probability_test_bounds {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∑ i, p i * f i ∧ ∑ i, p i * f i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hf i).1), ?_⟩
  calc
    ∑ i, p i * f i ≤ ∑ i, p i * 1 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i).2 (hp i))
    _ = 1 := by simpa only [mul_one] using hpsum

/-- Probability normalization gives the bound without a cardinality factor. -/
theorem centered_atom_mixture_test_error {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ) (t : ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) (ht : 0 ≤ t)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    |(∑ i, centeredAtomMixture p q t i * f i) - ∑ i, p i * f i| ≤ t := by
  have hP := finite_probability_test_bounds p f hp hpsum hf
  have hQ := finite_probability_test_bounds q f hq hqsum hf
  have hden : 0 < 1 + t := by positivity
  have heq : (∑ i, centeredAtomMixture p q t i * f i) =
      ((∑ i, p i * f i) + t * ∑ i, q i * f i) / (1 + t) := by
    simp only [centeredAtomMixture, div_mul_eq_mul_div, add_mul, mul_assoc,
      ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [heq]
  apply abs_le.mpr
  constructor
  · have hh : (∑ i, p i * f i) - t ≤
        ((∑ i, p i * f i) + t * ∑ i, q i * f i) / (1 + t) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [mul_nonneg ht hQ.1, mul_nonneg ht (sub_nonneg.mpr hP.2)]
    linarith
  · have hh : ((∑ i, p i * f i) + t * ∑ i, q i * f i) / (1 + t) ≤
        t + ∑ i, p i * f i := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg ht hP.1, mul_nonneg ht (sub_nonneg.mpr hQ.2)]
    linarith

theorem finite_zero_barycentric_weights_unique
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (w : ι → E) (ha : AffineIndependent ℝ w) (p q : ι → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hpmean : ∑ i, p i • w i = 0) (hqmean : ∑ i, q i • w i = 0) : p = q := by
  classical
  have hp' : ∑ i ∈ Finset.univ, p i = 1 := by simpa using hp
  have hq' : ∑ i ∈ Finset.univ, q i = 1 := by simpa using hq
  have heq : Finset.univ.affineCombination ℝ w p = Finset.univ.affineCombination ℝ w q := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hp',
      Finset.affineCombination_eq_linear_combination _ _ _ hq']
    simpa using hpmean.trans hqmean.symm
  exact funext (fun i => (ha.affineCombination_eq_iff_eq hp' hq').mp heq i (Finset.mem_univ i))

theorem exists_correcting_probability_on_same_atoms
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → E) (z : E) (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (hz : ‖z‖ ≤ h) (hball : closedBall (0 : E) b ⊆ convexHull ℝ (Set.range w)) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • w i = -((b⁻¹ * h)⁻¹ • z) := by
  have ht : 0 < b⁻¹ * h := mul_pos (inv_pos.mpr hb) hh
  apply finite_convex_hull_probability_weights
  apply hball
  rw [mem_closedBall, dist_zero_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht)]
  calc
    (b⁻¹ * h)⁻¹ * ‖z‖ ≤ (b⁻¹ * h)⁻¹ * h :=
      mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr ht.le)
    _ = b := by field_simp [hb.ne', hh.ne']

/-- The supplied atoms are retained. When h=0 the supplied law is retained exactly. -/
theorem exists_centered_atom_correction
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → E) (p : ι → ℝ) (b h : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (hb : 0 < b) (hh : 0 ≤ h)
    (hz : ‖∑ i, p i • w i‖ ≤ h)
    (hball : closedBall (0 : E) b ⊆ convexHull ℝ (Set.range w)) :
    ∃ β : ι → ℝ, (∀ i, 0 ≤ β i) ∧ ∑ i, β i = 1 ∧
      (∑ i, β i • w i = 0) ∧ (h = 0 → β = p) ∧
      ∀ f : ι → ℝ, (∀ i, 0 ≤ f i ∧ f i ≤ 1) →
        |(∑ i, β i * f i) - ∑ i, p i * f i| ≤ b⁻¹ * h := by
  by_cases hh0 : h = 0
  · have hz0 : ∑ i, p i • w i = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa only [hh0] using hz) (norm_nonneg _))
    refine ⟨p, hp, hpsum, hz0, fun _ => rfl, ?_⟩
    intro f _
    simp only [sub_self, abs_zero, hh0, mul_zero, le_refl]
  · have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    obtain ⟨q, hq, hqsum, hqmean⟩ :=
      exists_correcting_probability_on_same_atoms w (∑ i, p i • w i) b h hb hpos hz hball
    have ht : 0 < b⁻¹ * h := mul_pos (inv_pos.mpr hb) hpos
    obtain ⟨hβ, hβsum⟩ := centered_atom_mixture_probability p q (b⁻¹ * h) hp hq hpsum hqsum ht.le
    refine ⟨centeredAtomMixture p q (b⁻¹ * h), hβ, hβsum, ?_,
      fun h0 => False.elim (hh0 h0), ?_⟩
    · rw [centered_atom_mixture_mean, hqmean, smul_neg, smul_smul,
        mul_inv_cancel₀ ht.ne', one_smul, add_neg_cancel, smul_zero]
    · intro f hf
      exact centered_atom_mixture_test_error p q f (b⁻¹ * h) hp hq hpsum hqsum ht.le hf

section AssignedWeights

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Actual masses of the supplied measurable assignment fibers. -/
def assignedAtomWeights (ν : Measure α) (r : α → ι) : ι → ℝ :=
  fun i => (ν.map r).real {i}

theorem assigned_atom_weights_probability (ν : Measure α) [IsProbabilityMeasure ν]
    (r : α → ι) :
    (∀ i, 0 ≤ assignedAtomWeights ν r i) ∧ ∑ i, assignedAtomWeights ν r i = 1 := by
  classical
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  simp [assignedAtomWeights]

theorem assigned_atom_weights_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) [IsProbabilityMeasure ν] (r : α → ι) (hr : Measurable r) (f : ι → E) :
    ∑ i, assignedAtomWeights ν r i • f i = ∫ x, f (r x) ∂ν := by
  rw [← integral_map hr.aemeasurable
    (Integrable.of_finite : Integrable f (ν.map r)).aestronglyMeasurable]
  exact (integral_fintype (Integrable.of_finite : Integrable f (ν.map r))).symm

theorem assigned_atom_barycenter_norm_le_cost
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) [IsProbabilityMeasure ν] (X : α → E) (hX : Integrable X ν)
    (hcenter : (∫ x, X x ∂ν) = 0) (w : ι → E) (r : α → ι) (hr : Measurable r) :
    ‖∑ i, assignedAtomWeights ν r i • w i‖ ≤ ∫ x, ‖X x - w (r x)‖ ∂ν := by
  have hY : Integrable (fun x => w (r x)) ν :=
    (Integrable.of_finite : Integrable w (ν.map r)).comp_measurable hr
  rw [assigned_atom_weights_integral ν r hr w]
  calc
    ‖∫ x, w (r x) ∂ν‖ = ‖∫ x, w (r x) - X x ∂ν‖ := by
      rw [integral_sub hY hX, hcenter, sub_zero]
    _ ≤ ∫ x, ‖w (r x) - X x‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_sub_rev]

theorem assigned_atom_absolute_direction_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) [IsProbabilityMeasure ν] (X : α → E) (hX : Integrable X ν)
    (w : ι → E) (r : α → ι) (hr : Measurable r) (u : E) (hu : ‖u‖ = 1) :
    |(∑ i, assignedAtomWeights ν r i * |inner ℝ u (w i)|) -
      ∫ x, |inner ℝ u (X x)| ∂ν| ≤ ∫ x, ‖X x - w (r x)‖ ∂ν := by
  have hY : Integrable (fun x => w (r x)) ν :=
    (Integrable.of_finite : Integrable w (ν.map r)).comp_measurable hr
  have hdotX : Integrable (fun x => inner ℝ u (X x)) ν := (innerSL ℝ u).integrable_comp hX
  have hdotY : Integrable (fun x => inner ℝ u (w (r x))) ν := (innerSL ℝ u).integrable_comp hY
  have herr : Integrable (fun x => ‖X x - w (r x)‖) ν := (hX.sub hY).norm
  have heq : (∑ i, assignedAtomWeights ν r i * |inner ℝ u (w i)|) =
      ∫ x, |inner ℝ u (w (r x))| ∂ν := by
    simpa only [smul_eq_mul] using assigned_atom_weights_integral ν r hr (fun i => |inner ℝ u (w i)|)
  rw [heq, ← integral_sub hdotY.abs hdotX.abs]
  calc
    |∫ x, |inner ℝ u (w (r x))| - |inner ℝ u (X x)| ∂ν| ≤
        ∫ x, abs (|inner ℝ u (w (r x))| - |inner ℝ u (X x)|) ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖X x - w (r x)‖ ∂ν := by
      apply integral_mono (hdotY.abs.sub hdotX.abs).abs herr
      intro x
      calc
        abs (|inner ℝ u (w (r x))| - |inner ℝ u (X x)|) ≤
            |inner ℝ u (w (r x)) - inner ℝ u (X x)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |inner ℝ u (w (r x) - X x)| := by rw [inner_sub_right]
        _ ≤ ‖X x - w (r x)‖ := by
          simpa only [hu, one_mul, norm_sub_rev] using abs_real_inner_le_norm u (w (r x) - X x)

end AssignedWeights

theorem finite_centered_negative_eq_half_absolute
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → E) (β : ι → ℝ) (hmean : ∑ i, β i • w i = 0) (u : E) :
    (∑ i, β i * max (-inner ℝ u (w i)) 0) = (∑ i, β i * |inner ℝ u (w i)|) / 2 := by
  have hdot : ∑ i, β i * inner ℝ u (w i) = 0 := by
    simpa only [inner_sum, real_inner_smul_right, inner_zero_right] using
      congrArg (fun z => inner ℝ u z) hmean
  have hpoint (i : ι) : β i * |inner ℝ u (w i)| =
      β i * inner ℝ u (w i) + 2 * (β i * max (-inner ℝ u (w i)) 0) := by
    rcases le_total 0 (inner ℝ u (w i)) with hi | hi
    · rw [abs_of_nonneg hi, max_eq_right (neg_nonpos.mpr hi)]
      ring
    · rw [abs_of_nonpos hi, max_eq_left (neg_nonneg.mpr hi)]
      ring
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdot, zero_add] at hsum
  linarith

theorem centered_integral_negative_eq_half_absolute
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) (X : α → E) (hX : Integrable X ν)
    (hcenter : (∫ x, X x ∂ν) = 0) (u : E) :
    negativeIntegral ν (fun x => inner ℝ u (X x)) =
      (∫ x, |inner ℝ u (X x)| ∂ν) / 2 := by
  have hdot : Integrable (fun x => inner ℝ u (X x)) ν := (innerSL ℝ u).integrable_comp hX
  have hm0 : (∫ x, inner ℝ u (X x) ∂ν) = 0 := by
    simpa only [innerSL_apply_apply, hcenter, inner_zero_right] using
      (innerSL ℝ u).integral_comp_comm hX
  have hm := integral_mean_decomposition hdot
  have ha := integral_absolute_decomposition hdot
  rw [hm0] at hm
  linarith

/-- Actual transport to the supplied atoms followed by probability centering.
The directional brightness error has no factor depending on the number of atoms. -/
theorem exists_centered_assigned_atom_brightness
    {α ι E : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) [IsProbabilityMeasure ν] (X : α → E) (hX : Integrable X ν)
    (hcenter : (∫ x, X x ∂ν) = 0) (w : ι → E) (hw : ∀ i, ‖w i‖ ≤ 1)
    (r : α → ι) (hr : Measurable r) (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h)
    (hcost : (∫ x, ‖X x - w (r x)‖ ∂ν) ≤ h)
    (hball : closedBall (0 : E) b ⊆ convexHull ℝ (Set.range w)) :
    ∃ β : ι → ℝ, (∀ i, 0 ≤ β i) ∧ ∑ i, β i = 1 ∧
      (∑ i, β i • w i = 0) ∧ (h = 0 → β = assignedAtomWeights ν r) ∧
      ∀ u : E, ‖u‖ = 1 →
        |(∑ i, β i * max (-inner ℝ u (w i)) 0) -
          negativeIntegral ν (fun x => inner ℝ u (X x))| ≤ (b⁻¹ + 1) * h / 2 := by
  obtain ⟨hp, hpsum⟩ := assigned_atom_weights_probability ν r
  obtain ⟨β, hβ, hβsum, hβmean, hβzero, hβtest⟩ :=
    exists_centered_atom_correction w (assignedAtomWeights ν r) b h hp hpsum hb hh
      ((assigned_atom_barycenter_norm_le_cost ν X hX hcenter w r hr).trans hcost) hball
  refine ⟨β, hβ, hβsum, hβmean, hβzero, ?_⟩
  intro u hu
  have htest : ∀ i, 0 ≤ |inner ℝ u (w i)| ∧ |inner ℝ u (w i)| ≤ 1 := by
    intro i
    refine ⟨abs_nonneg _, ?_⟩
    simpa only [hu, one_mul] using (abs_real_inner_le_norm u (w i)).trans
      (mul_le_mul_of_nonneg_left (hw i) (norm_nonneg u))
  have hcor := hβtest (fun i => |inner ℝ u (w i)|) htest
  have hassign := (assigned_atom_absolute_direction_error ν X hX w r hr u hu).trans hcost
  have hall : |(∑ i, β i * |inner ℝ u (w i)|) - ∫ x, |inner ℝ u (X x)| ∂ν| ≤
      b⁻¹ * h + h := by
    calc
      |(∑ i, β i * |inner ℝ u (w i)|) - ∫ x, |inner ℝ u (X x)| ∂ν| ≤
          abs ((∑ i, β i * |inner ℝ u (w i)|) -
            ∑ i, assignedAtomWeights ν r i * |inner ℝ u (w i)|) +
          |(∑ i, assignedAtomWeights ν r i * |inner ℝ u (w i)|) -
            ∫ x, |inner ℝ u (X x)| ∂ν| := abs_sub_le _ _ _
      _ ≤ b⁻¹ * h + h := add_le_add hcor hassign
  rw [finite_centered_negative_eq_half_absolute w β hβmean u,
    centered_integral_negative_eq_half_absolute ν X hX hcenter u, ← sub_div, abs_div]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (b⁻¹ * h + h) / 2 := div_le_div_of_nonneg_right hall (by norm_num)
    _ = _ := by ring

theorem zero_barycentric_weights_assigned_brightness
    {α ι E : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) [IsProbabilityMeasure ν] (X : α → E) (hX : Integrable X ν)
    (hcenter : (∫ x, X x ∂ν) = 0) (w : ι → E) (hw : ∀ i, ‖w i‖ ≤ 1)
    (ha : AffineIndependent ℝ w) (c : ι → ℝ) (hcsum : ∑ i, c i = 1)
    (hcmean : ∑ i, c i • w i = 0)
    (r : α → ι) (hr : Measurable r) (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h)
    (hcost : (∫ x, ‖X x - w (r x)‖ ∂ν) ≤ h)
    (hball : closedBall (0 : E) b ⊆ convexHull ℝ (Set.range w)) :
    (∀ i, 0 ≤ c i) ∧ (h = 0 → c = assignedAtomWeights ν r) ∧
      ∀ u : E, ‖u‖ = 1 →
        |(∑ i, c i * max (-inner ℝ u (w i)) 0) -
          negativeIntegral ν (fun x => inner ℝ u (X x))| ≤ (b⁻¹ + 1) * h / 2 := by
  obtain ⟨β, hβ, hβsum, hβmean, hβzero, hβbrightness⟩ :=
    exists_centered_assigned_atom_brightness ν X hX hcenter w hw r hr b h hb hh hcost hball
  have heq := finite_zero_barycentric_weights_unique w ha β c hβsum hcsum hβmean hcmean
  subst c
  exact ⟨hβ, hβzero, hβbrightness⟩

theorem finite_atom_negative_integral_eq_weighted
    {ι : Type*} [Fintype ι] {d : ℕ} (p : ι → ℝ) (w : ι → Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (u : Fin d → ℝ) :
    negativeIntegral (finiteAtomLaw p w) (fun x => dotProduct u x) =
      ∑ i, p i * max (-dotProduct u (w i)) 0 := by
  rw [finite_atom_law_eq_cone, negativeIntegral,
    finite_cone_integral p (fun _ => 1) w 1 hp (fun _ => by norm_num) (by norm_num)]
  simp only [finite_cone_point_height_one, mul_one, div_one]

/-- Direct raw-coordinate law form of the centered correction estimate. -/
theorem raw_zero_barycentric_weights_assignment_brightness
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hνball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hνcenter : ∀ j, (∫ x, x j ∂ν) = 0)
    (w : ι → Fin d → ℝ) (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (ha : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)))
    (c : ι → ℝ) (hcsum : ∑ i, c i = 1)
    (hcmean : ∑ i, c i • WithLp.toLp 2 (w i) = 0)
    (r : (Fin d → ℝ) → ι) (hr : Measurable r)
    (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤ h)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin d)) b ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i)))) :
    (∀ i, 0 ≤ c i) ∧ (h = 0 → c = assignedAtomWeights ν r) ∧
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
        |negativeIntegral (finiteAtomLaw c w) (fun x => dotProduct u x) -
          negativeIntegral ν (fun x => dotProduct u x)| ≤ (b⁻¹ + 1) * h / 2 := by
  have hX : Integrable (fun x : Fin d → ℝ => WithLp.toLp 2 x) ν := by
    apply (integrable_const (1 : ℝ)).mono'
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.aestronglyMeasurable
    exact hνball
  have hcenter : (∫ x : Fin d → ℝ, WithLp.toLp 2 x ∂ν) = 0 := by
    ext j
    have heq := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) j).integral_comp_comm hX
    simpa only [PiLp.proj_apply, WithLp.ofLp_toLp, hνcenter j,
      PiLp.zero_apply] using heq.symm
  obtain ⟨hc, hc0, hcbright⟩ := zero_barycentric_weights_assigned_brightness
    ν (fun x : Fin d → ℝ => WithLp.toLp 2 x) hX hcenter
    (fun i => WithLp.toLp 2 (w i)) hw ha c hcsum hcmean r hr b h hb hh hcost hball
  refine ⟨hc, hc0, ?_⟩
  intro u hu
  rw [finite_atom_negative_integral_eq_weighted c w hc u]
  simpa only [euclidean_inner_raw] using hcbright u hu

end Entry005
