import Entry005.ProjectionVolumeSqueeze
import Entry005.Constants
import Entry005.BallVolume
import Mathlib.Algebra.Order.Ring.Abs

/-!
Independent scale leaves for the sharp assembly. The actual volume-ratio
inequality is an explicit geometric input; no Minkowski first inequality or
volume-derivative theorem is asserted by this module.
-/

noncomputable section
open Metric MeasureTheory
open scoped BigOperators

namespace Entry005

theorem euclidean_closed_ball_volume_le_cube (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : Space d) R)).toReal ≤ (2 * R) ^ d := by
  let C : Set (Fin d → ℝ) := Set.Icc (fun _ => -R) (fun _ => R)
  have hsubset : (WithLp.toLp 2) ⁻¹' closedBall (0 : Space d) R ⊆ C := by
    intro x hx
    have hxnorm : ‖WithLp.toLp 2 x‖ ≤ R := by
      simpa [mem_closedBall, dist_zero_right] using hx
    have hxi (i : Fin d) : |x i| ≤ R := by
      have hcoord : |x i| ≤ ‖WithLp.toLp 2 x‖ := by
        simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (WithLp.toLp 2 x) i)
      exact hcoord.trans hxnorm
    exact ⟨fun i => (abs_le.mp (hxi i)).1, fun i => (abs_le.mp (hxi i)).2⟩
  have hC : IsCompact C := isCompact_Icc
  have hvol : (volume C).toReal = (2 * R) ^ d := by
    rw [Real.volume_Icc_pi_toReal (fun _ => by linarith : (fun _ : Fin d => -R) ≤ fun _ => R)]
    simp [sub_neg_eq_add, ← two_mul]
  calc
    (volume (closedBall (0 : Space d) R)).toReal =
        (volume ((WithLp.toLp 2) ⁻¹' closedBall (0 : Space d) R)).toReal := by
      rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
        measurableSet_closedBall.nullMeasurableSet]
    _ ≤ (volume C).toReal := ENNReal.toReal_mono hC.measure_ne_top (measure_mono hsubset)
    _ = (2 * R) ^ d := hvol

theorem bounded_body_volume_le_cube {d : ℕ} (K : Set (Space d)) (R : ℝ)
    (hR : 0 ≤ R) (hbound : K ⊆ closedBall (0 : Space d) R) :
    (volume K).toReal ≤ (2 * R) ^ d :=
  (compact_real_volume_mono K _ (isCompact_closedBall _ _) hbound).trans
    (euclidean_closed_ball_volume_le_cube d R hR)

theorem unit_increment_power_bound (d : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) ^ d - 1 ≤ (d : ℝ) * (2 : ℝ) ^ (d - 1) * t := by
  have hp := abs_pow_sub_pow_le (a := 1 + t) (b := (1 : ℝ)) (n := d)
  have hm : max |1 + t| |(1 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by linarith), abs_one]
    exact max_le (by linarith) (by norm_num)
  have hpow : max |1 + t| |(1 : ℝ)| ^ (d - 1) ≤ (2 : ℝ) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) hm _
  have hmulp := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ |1 + t - 1| * (d : ℝ) by positivity)
  have h := (le_abs_self ((1 + t) ^ d - 1)).trans (by simpa using hp)
  have hs : |1 + t - 1| = t := by rw [add_sub_cancel_left, abs_of_nonneg ht]
  rw [hs] at hmulp
  calc
    (1 + t) ^ d - 1 ≤ t * (d : ℝ) * max |1 + t| |(1 : ℝ)| ^ (d - 1) := by
      simpa [hs, abs_of_nonneg ht] using h
    _ ≤ t * (d : ℝ) * (2 : ℝ) ^ (d - 1) := hmulp
    _ = (d : ℝ) * (2 : ℝ) ^ (d - 1) * t := by ring

theorem scale_increment_of_volume_ratio {d : ℕ} (alpha M h : ℝ)
    (hM : 0 ≤ M) (hh : 0 ≤ h) (hsmall : M * h ≤ 1)
    (hscale : alpha ≤ (1 + M * h) ^ d) :
    alpha - 1 ≤ (d : ℝ) * (2 : ℝ) ^ (d - 1) * M * h := by
  have hp := unit_increment_power_bound d (M * h) (mul_nonneg hM hh) hsmall
  nlinarith

theorem projection_difference_of_normalized_brightness {d : ℕ} (hd : 1 ≤ d)
    (V alpha k p M h : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (halpha : 1 ≤ alpha) (hscale : alpha ≤ (1 + M * h) ^ d)
    (hsmall : M * h ≤ 1) (hp : p ≤ 1 / 2)
    (hbright : |p - k| ≤ (M + 1) * h / 2) :
    (d : ℝ) * V * (alpha * p - k) ≤
      (d : ℝ) / 2 * V * (1 + M + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M) * h := by
  have hinc := scale_increment_of_volume_ratio alpha M h hM hh hsmall hscale
  have hmult := mul_le_mul_of_nonneg_left hp (show 0 ≤ alpha - 1 by linarith)
  have hdiff : p - k ≤ (M + 1) * h / 2 := (le_abs_self _).trans hbright
  have hinside : alpha * p - k ≤
      (1 + M + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M) * h / 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hinside (show 0 ≤ (d : ℝ) * V by positivity)
  convert hmul using 1; ring

theorem actual_projection_deficit_of_scale_and_brightness {d : ℕ} (hd : 1 ≤ d)
    (K P : Set (Space d)) (hcK : IsCompact K) (hcP : IsCompact P)
    (hball : closedBall (0 : Space d) 1 ⊆ K) (hKP : K ⊆ P)
    (hbound : K ⊆ closedBall (0 : Space d) (R0 d)) (h : ℝ) (hh : 0 ≤ h)
    (hsmall : M d * h ≤ 1)
    (hscale : (volume P).toReal / (volume K).toReal ≤ (1 + M d * h) ^ d)
    (hbright : ∀ u : Space d, ‖u‖ = 1 →
      |projectionVolumeSet P u / ((d : ℝ) * (volume P).toReal) -
        projectionVolumeSet K u / ((d : ℝ) * (volume K).toReal)| ≤ (M d + 1) * h / 2)
    (hPbright : ∀ u : Space d, ‖u‖ = 1 →
      projectionVolumeSet P u / ((d : ℝ) * (volume P).toReal) ≤ 1 / 2) :
    ∀ u : Space d, ‖u‖ = 1 → projectionVolumeSet P u - projectionVolumeSet K u ≤ J d * h := by
  have hV : 0 < (volume K).toReal := compact_body_volume_pos_of_unit_ball K hcK hball
  have hVP : 0 < (volume P).toReal := compact_body_volume_pos_of_unit_ball P hcP (hball.trans hKP)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have halpha : 1 ≤ (volume P).toReal / (volume K).toReal :=
    (one_le_div hV).mpr (compact_real_volume_mono K P hcP hKP)
  have hcube := bounded_body_volume_le_cube K (R0 d) (R0_pos hd).le hbound
  intro u hu
  have hp := projection_difference_of_normalized_brightness hd
    (volume K).toReal ((volume P).toReal / (volume K).toReal)
    (projectionVolumeSet K u / ((d : ℝ) * (volume K).toReal))
    (projectionVolumeSet P u / ((d : ℝ) * (volume P).toReal)) (M d) h
    hV.le (M_pos hd).le hh halpha hscale hsmall (hPbright u hu) (hbright u hu)
  have hid : (d : ℝ) * (volume K).toReal *
      ((volume P).toReal / (volume K).toReal *
        (projectionVolumeSet P u / ((d : ℝ) * (volume P).toReal)) -
        projectionVolumeSet K u / ((d : ℝ) * (volume K).toReal)) =
      projectionVolumeSet P u - projectionVolumeSet K u := by
    field_simp
  rw [hid] at hp
  have hcoef : 0 ≤ (d : ℝ) / 2 *
      (1 + M d + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M d) * h := by
    have := (M_pos hd).le
    positivity
  calc
    projectionVolumeSet P u - projectionVolumeSet K u ≤
        (d : ℝ) / 2 * (volume K).toReal *
          (1 + M d + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M d) * h := hp
    _ ≤ (d : ℝ) / 2 * (2 * R0 d) ^ d *
          (1 + M d + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M d) * h := by
      nlinarith [mul_le_mul_of_nonneg_right hcube hcoef]
    _ = J d * h := rfl

theorem actual_cap_bound_of_scale_and_brightness {d : ℕ} (hd : 2 ≤ d)
    (K P : ConvexBody (Space d))
    (hball : closedBall (0 : Space d) 1 ⊆ K) (hKP : K ≤ P)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (hPM : (P : Set (Space d)) ⊆ closedBall (0 : Space d) (M d))
    (h : ℝ) (hh : 0 ≤ h) (hsmall : M d * h ≤ 1)
    (hscale : (volume (P : Set (Space d))).toReal /
      (volume (K : Set (Space d))).toReal ≤ (1 + M d * h) ^ d)
    (hbright : ∀ u : Space d, ‖u‖ = 1 →
      |projectionVolumeSet (P : Set (Space d)) u /
          ((d : ℝ) * (volume (P : Set (Space d))).toReal) -
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal)| ≤ (M d + 1) * h / 2)
    (hPbright : ∀ u : Space d, ‖u‖ = 1 →
      projectionVolumeSet (P : Set (Space d)) u /
        ((d : ℝ) * (volume (P : Set (Space d))).toReal) ≤ 1 / 2) :
    Metric.hausdorffDist (K : Set (Space d)) (P : Set (Space d)) ≤
      L d * (J d * h) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hdef := actual_projection_deficit_of_scale_and_brightness hd1
    (K : Set (Space d)) (P : Set (Space d)) K.isCompact P.isCompact
    hball hKP hbound h hh hsmall hscale hbright hPbright
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  have hdef' : ∀ u : Space d, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ J d * h := by
    intro u hu
    change projectionVolumeSet (P : Set (Space d)) u -
      projectionVolumeSet (K : Set (Space d)) u ≤ J d * h
    exact hdef u hu
  have hcap := hausdorff_from_projection_deficit (by simpa only [hdim] using hd)
    K P (M d) (J d * h) (M_pos hd1).le (mul_nonneg (J_pos hd1).le hh)
    hball hKP hPM hdef'
  simpa only [hdim, L] using hcap

end Entry005
