import GaussianFour.AffineBoundary
import GaussianTailCalculus

/-! Truncating the actual one-dimensional Gaussian by an arbitrary measurable
mask. This is the slicing input for price derivatives at singular diagrams. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open GaussianMeasureBridge
namespace GaussianFour

noncomputable def maskedTail (s : Set ℝ) (a : ℝ) : ℝ :=
  ∫ x in Ioi a, s.indicator standardDensity x

lemma maskedDensity_norm_le (s : Set ℝ) (x : ℝ) :
    ‖s.indicator standardDensity x‖ ≤ standardDensity 0 := by
  classical
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos (standardDensity_pos x)]
    exact standardDensity_le_zero x
  · simp only [indicator_of_notMem hx, norm_zero]
    exact (standardDensity_pos 0).le

lemma maskedTail_sub (s : Set ℝ) (hs : MeasurableSet s) (a b : ℝ) :
    maskedTail s a - maskedTail s b = ∫ x in a..b, s.indicator standardDensity x :=
  intervalIntegral.integral_Ioi_sub_Ioi'
    ((integrable_gaussianPDFReal 0 1).indicator hs).integrableOn
    ((integrable_gaussianPDFReal 0 1).indicator hs).integrableOn

lemma maskedTail_lipschitz (s : Set ℝ) (hs : MeasurableSet s) :
    LipschitzWith ⟨standardDensity 0, (standardDensity_pos 0).le⟩ (maskedTail s) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm, maskedTail_sub s hs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun x _ => maskedDensity_norm_le s x)
  change ‖∫ x in a..b, s.indicator standardDensity x‖ ≤ standardDensity 0 * dist a b
  simpa only [Real.dist_eq, abs_sub_comm, mul_comm] using h

lemma maskedTail_nonneg (s : Set ℝ) (a : ℝ) : 0 ≤ maskedTail s a := by
  apply integral_nonneg
  intro x
  exact Set.indicator_nonneg (fun x _ => (standardDensity_pos x).le) x

lemma maskedTail_le_one (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ) :
    maskedTail s a ≤ 1 := by
  classical
  have hi : Integrable standardDensity := integrable_gaussianPDFReal 0 1
  have hle (x : ℝ) : s.indicator standardDensity x ≤ standardDensity x := by
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx, le_refl]
    · simpa only [indicator_of_notMem hx] using (standardDensity_pos x).le
  have h := integral_mono_ae (hi.indicator hs).integrableOn hi.integrableOn
    (ae_of_all (volume.restrict (Ioi a)) hle)
  change maskedTail s a ≤ ∫ x in Ioi a, standardDensity x at h
  rw [← standardTail_eq_integral] at h
  exact h.trans measureReal_le_one

/-- A boundary derivative needs continuity only at the moving cutoff; the
mask may be discontinuous elsewhere. -/
theorem maskedTail_hasDerivAt (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ)
    (hc : ContinuousAt (s.indicator standardDensity) a) :
    HasDerivAt (maskedTail s) (-s.indicator standardDensity a) a := by
  have hi : Integrable (s.indicator standardDensity) :=
    (integrable_gaussianPDFReal 0 1).indicator hs
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hi.intervalIntegrable (a := (0 : ℝ)) (b := a))
    ((continuous_standardDensity.stronglyMeasurable).indicator hs).stronglyMeasurableAtFilter hc
  have he : maskedTail s = fun b => maskedTail s 0 - ∫ x in (0 : ℝ)..b,
      s.indicator standardDensity x := by
    funext b
    have h := maskedTail_sub s hs 0 b
    linarith
  rw [he]
  exact hd.const_sub (maskedTail s 0)

lemma maskedTail_eq_gaussian_integral (s : Set ℝ) (a : ℝ) :
    maskedTail s a = ∫ x, (Ioi a ∩ s).indicator (fun _ : ℝ => (1 : ℝ)) x
      ∂gaussianReal 0 1 := by
  classical
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  rw [maskedTail, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ Ioi a <;> by_cases hxs : x ∈ s <;>
      simp [hx, hxs, standardDensity]

end GaussianFour
