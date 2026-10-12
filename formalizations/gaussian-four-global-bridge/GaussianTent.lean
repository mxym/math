import GaussianPartition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A bounded-density tent estimate on the actual standard Gaussian.
This is an analytic ingredient for uniform separation of balanced cell moments.
No isoperimetric, perimeter, or covariance comparison is assumed. -/

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace GaussianFourGlobal
open GaussianMeasureBridge

noncomputable def densityCap : ℝ := gaussianPDFReal 0 1 0

lemma densityCap_pos : 0 < densityCap := gaussianPDFReal_pos 0 1 0 one_ne_zero

lemma densityCap_eq : densityCap = (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp [densityCap, gaussianPDFReal]

lemma gaussianPDF_le_densityCap (x : ℝ) : gaussianPDFReal 0 1 x ≤ densityCap := by
  have he : Real.exp (-(x ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  simpa [gaussianPDFReal, densityCap] using mul_le_mul_of_nonneg_left he hc

noncomputable def tent (a t x : ℝ) : ℝ := max (a - |x - t|) 0

lemma tent_nonneg (a t x : ℝ) : 0 ≤ tent a t x := le_max_right _ _

lemma tent_le (a t x : ℝ) (ha : 0 ≤ a) : tent a t x ≤ a := by
  exact max_le (by linarith [abs_nonneg (x - t)]) ha

lemma continuous_tent (a t : ℝ) : Continuous (tent a t) := by
  unfold tent
  fun_prop

lemma tent_eq_zero_outside (a t x : ℝ) (hx : x ∉ Icc (t - a) (t + a)) :
    tent a t x = 0 := by
  apply max_eq_right
  by_contra h
  have hlt : |x - t| < a := by linarith
  have hpair := abs_lt.mp hlt
  exact hx ⟨by linarith [hpair.1], by linarith [hpair.2]⟩

lemma integrable_tent (a t : ℝ) : Integrable (tent a t) := by
  apply (continuous_tent a t).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra h
  exact hx (tent_eq_zero_outside a t x h)

/-- The exact Lebesgue area of a tent, including its zero-width boundary. -/
theorem integral_tent (a t : ℝ) (ha : 0 ≤ a) : (∫ x, tent a t x) = a ^ 2 := by
  have hleft : (∫ x in (t - a)..t, tent a t x) = a ^ 2 / 2 := by
    calc
      _ = ∫ x in (t - a)..t, (a - t) + x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : t - a ≤ t)] at hx
        rw [tent, abs_of_nonpos (by linarith [hx.2]), max_eq_left (by linarith [hx.1])]
        ring
      _ = a ^ 2 / 2 := by
        rw [intervalIntegral.integral_add (f := fun _ : ℝ => a - t) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _)
          (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const,
          _root_.integral_id]
        simp only [smul_eq_mul]
        ring
  have hright : (∫ x in t..(t + a), tent a t x) = a ^ 2 / 2 := by
    calc
      _ = ∫ x in t..(t + a), (a + t) - x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : t ≤ t + a)] at hx
        rw [tent, abs_of_nonneg (by linarith [hx.1]), max_eq_left (by linarith [hx.2])]
        ring
      _ = a ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub (f := fun _ : ℝ => a + t) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _)
          (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const,
          _root_.integral_id]
        simp only [smul_eq_mul]
        ring
  calc
    _ = ∫ x in Icc (t - a) (t + a), tent a t x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => tent_eq_zero_outside a t x hx)).symm
    _ = ∫ x in (t - a)..(t + a), tent a t x := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    _ = (∫ x in (t - a)..t, tent a t x) + (∫ x in t..(t + a), tent a t x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_tent a t).intervalIntegrable _ _)
        ((continuous_tent a t).intervalIntegrable _ _)).symm
    _ = a ^ 2 := by rw [hleft, hright]; ring

/-- Gaussian tent domination by the exact uniform-density tent area. -/
theorem gaussianReal_tent_bound (a t : ℝ) (ha : 0 ≤ a) :
    (∫ x, tent a t x ∂gaussianReal 0 1) ≤ densityCap * a ^ 2 := by
  have hi : Integrable (fun x => gaussianPDFReal 0 1 x * tent a t x) :=
    (integrable_tent a t).bdd_mul (measurable_gaussianPDFReal 0 1).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
        exact gaussianPDF_le_densityCap x)
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x, densityCap * tent a t x :=
      integral_mono hi ((integrable_tent a t).const_mul densityCap)
        (fun x => mul_le_mul_of_nonneg_right (gaussianPDF_le_densityCap x) (tent_nonneg a t x))
    _ = densityCap * a ^ 2 := by rw [integral_const_mul, integral_tent a t ha]

lemma unit_inner_law {d : ℕ} (u : Space d) (hu : ‖u‖ = 1) :
    (gaussian d).map (fun x => ⟪u, x⟫) = gaussianReal 0 1 := by
  change (gaussian d).map (innerSL ℝ u) = _
  rw [IsGaussian.map_eq_gaussianReal, gaussian, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, hu]
  norm_num

theorem gaussian_inner_tent_bound {d : ℕ} (u : Space d) (hu : ‖u‖ = 1)
    (a t : ℝ) (ha : 0 ≤ a) :
    (∫ x, tent a t ⟪u, x⟫ ∂gaussian d) ≤ densityCap * a ^ 2 := by
  have h := gaussianReal_tent_bound a t ha
  rw [← unit_inner_law u hu,
    integral_map (by fun_prop) (continuous_tent a t).measurable.aestronglyMeasurable] at h
  exact h

lemma integrable_inner_tent {d : ℕ} (u : Space d) (a t : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x => tent a t ⟪u, x⟫) (gaussian d) := by
  apply (integrable_const a).mono' (by unfold tent; fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg a t ⟪u, x⟫)]
    exact tent_le a t ⟪u, x⟫ ha

end GaussianFourGlobal
