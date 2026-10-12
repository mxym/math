import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real probability-law cancellation and two-sample integrated witnesses.
This module does not assert the cone-law representation or determinant conditioning.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def positiveIntegral (μ : Measure α) (f : α → ℝ) : ℝ := ∫ x, max (f x) 0 ∂μ
def negativeIntegral (μ : Measure α) (f : α → ℝ) : ℝ := ∫ x, max (-f x) 0 ∂μ
def cancellationDefect (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, |f x| ∂μ) - |∫ x, f x ∂μ|
def oppositeWitness (a b : ℝ) : ℝ :=
  min (max a 0) (max (-b) 0) + min (max (-a) 0) (max b 0)

theorem integral_mean_decomposition {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = positiveIntegral μ f - negativeIntegral μ f := by
  have hpoint : ∀ x, f x = max (f x) 0 - max (-f x) 0 := by intro x; grind
  simp only [positiveIntegral, negativeIntegral]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_sub hf.pos_part hf.neg_part]

theorem integral_absolute_decomposition {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x| ∂μ) = positiveIntegral μ f + negativeIntegral μ f := by
  have hpoint : ∀ x, |f x| = max (f x) 0 + max (-f x) 0 := by intro x; grind
  simp only [positiveIntegral, negativeIntegral]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_add hf.pos_part hf.neg_part]

theorem integral_cancellation_identity {f : α → ℝ} (hf : Integrable f μ) :
    cancellationDefect μ f = 2 * min (positiveIntegral μ f) (negativeIntegral μ f) := by
  unfold cancellationDefect
  rw [integral_mean_decomposition hf, integral_absolute_decomposition hf]
  rcases le_total (positiveIntegral μ f) (negativeIntegral μ f) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

theorem cancellation_defect_nonneg {f : α → ℝ} (hf : Integrable f μ) :
    0 ≤ cancellationDefect μ f := by
  rw [integral_cancellation_identity hf]
  apply mul_nonneg (by norm_num)
  exact le_min (integral_nonneg fun x => le_max_right _ _)
    (integral_nonneg fun x => le_max_right _ _)

theorem opposite_witness_nonneg (a b : ℝ) : 0 ≤ oppositeWitness a b := by
  unfold oppositeWitness
  exact add_nonneg (le_min (le_max_right _ _) (le_max_right _ _))
    (le_min (le_max_right _ _) (le_max_right _ _))

theorem opposite_witness_integrable [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) :
    Integrable (fun z : α × α => oppositeWitness (f z.1) (f z.2)) (μ.prod μ) := by
  exact ((hf.pos_part.comp_fst μ).inf (hf.neg_part.comp_snd μ)).add
    ((hf.neg_part.comp_fst μ).inf (hf.pos_part.comp_snd μ))

theorem integrated_opposite_witness_le [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) :
    (∫ z : α × α, oppositeWitness (f z.1) (f z.2) ∂μ.prod μ) ≤
      cancellationDefect μ f := by
  let a : α × α → ℝ := fun z => min (max (f z.1) 0) (max (-f z.2) 0)
  let b : α × α → ℝ := fun z => min (max (-f z.1) 0) (max (f z.2) 0)
  have ha : Integrable a (μ.prod μ) := (hf.pos_part.comp_fst μ).inf (hf.neg_part.comp_snd μ)
  have hb : Integrable b (μ.prod μ) := (hf.neg_part.comp_fst μ).inf (hf.pos_part.comp_snd μ)
  have haP : (∫ z, a z ∂μ.prod μ) ≤ positiveIntegral μ f := by
    have h := integral_mono ha (hf.pos_part.comp_fst μ) (fun z => min_le_left _ _)
    rw [integral_fun_fst (fun x => max (f x) 0)] at h
    simpa [positiveIntegral] using h
  have haN : (∫ z, a z ∂μ.prod μ) ≤ negativeIntegral μ f := by
    have h := integral_mono ha (hf.neg_part.comp_snd μ) (fun z => min_le_right _ _)
    rw [integral_fun_snd (fun x => max (-f x) 0)] at h
    simpa [negativeIntegral] using h
  have hbN : (∫ z, b z ∂μ.prod μ) ≤ negativeIntegral μ f := by
    have h := integral_mono hb (hf.neg_part.comp_fst μ) (fun z => min_le_left _ _)
    rw [integral_fun_fst (fun x => max (-f x) 0)] at h
    simpa [negativeIntegral] using h
  have hbP : (∫ z, b z ∂μ.prod μ) ≤ positiveIntegral μ f := by
    have h := integral_mono hb (hf.pos_part.comp_snd μ) (fun z => min_le_right _ _)
    rw [integral_fun_snd (fun x => max (f x) 0)] at h
    simpa [positiveIntegral] using h
  change (∫ z, a z + b z ∂μ.prod μ) ≤ _
  rw [integral_add ha hb, integral_cancellation_identity hf]
  linarith [le_min haP haN, le_min hbP hbN]

theorem exists_conditioned_low_witness [IsFiniteMeasure μ] {H : α → ℝ}
    (hH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x) {s : Set α}
    {q B : ℝ} (hq : 0 < q) (hs : q ≤ (μ s).toReal)
    (hmean : (∫ x, H x ∂μ) ≤ B) :
    ∃ x ∈ s, H x ≤ B / q := by
  have hmass : 0 < (μ s).toReal := lt_of_lt_of_le hq hs
  have hne : μ s ≠ 0 := by intro h; simp [h] at hmass
  obtain ⟨x, hx, hlow⟩ := exists_le_setAverage hne (measure_ne_top μ s) hH.integrableOn
  have hB : 0 ≤ B := le_trans (integral_nonneg hH0) hmean
  have hrestricted : (∫ x in s, H x ∂μ) ≤ B :=
    (integral_mono_measure μ.restrict_le_self
      (Filter.Eventually.of_forall hH0) hH).trans hmean
  refine ⟨x, hx, hlow.trans ?_⟩
  rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_right hrestricted hmass.le).trans
    (div_le_div_of_nonneg_left hB hq hs)

theorem exists_conditioned_low_witness_ae_good [IsFiniteMeasure μ] {H : α → ℝ}
    (hH : Integrable H μ) (hH0 : ∀ x, 0 ≤ H x) {s : Set α} {G : α → Prop}
    (hG : ∀ᵐ x ∂μ, G x) {q B : ℝ} (hq : 0 < q) (hs : q ≤ (μ s).toReal)
    (hmean : (∫ x, H x ∂μ) ≤ B) :
    ∃ x ∈ s, G x ∧ H x ≤ B / q := by
  have hsame : μ {x | x ∈ s ∧ G x} = μ s := by
    apply measure_congr
    filter_upwards [hG] with x hx
    simp only [hx, and_true]
  obtain ⟨x, hx, hlow⟩ := exists_conditioned_low_witness hH hH0 hq
    (hsame.symm ▸ hs) hmean
  exact ⟨x, hx.1, hx.2, hlow⟩

end Entry005
