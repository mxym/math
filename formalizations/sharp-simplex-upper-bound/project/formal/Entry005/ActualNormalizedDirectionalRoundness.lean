import Entry005.ProjectionScaleAssembly
import Entry005.IidTransport

/-! Actual normalized-body roundness from actual unit projection-ball and
ambient cube volumes. The supplied law is retained throughout. -/

noncomputable section
open Metric MeasureTheory
open scoped BigOperators

namespace Entry005

/-- The literal Euclidean unit projection ball has the coarse volume required
by the original constant, proved through the actual inscribed cube. -/
theorem unit_projection_ball_volume_lower_original {d : ℕ} (hd : 2 ≤ d) :
    (2 / (d : ℝ)) ^ (d - 1) ≤ unitProjectionBallVolume d := by
  have hm : 1 ≤ d - 1 := by omega
  have hmp : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hmd : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hbase : 2 / (d : ℝ) ≤ 2 / ((d - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hmp hmd
  have hc := euclidean_unit_ball_cube (d - 1) hm
  have hv := ENNReal.toReal_mono
    (isCompact_closedBall (0 : Space (d - 1)) (1 : ℝ)).measure_ne_top hc
  have hpow : (2 / ((d - 1 : ℕ) : ℝ)) ^ (d - 1) ≤ unitProjectionBallVolume d := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 / ((d - 1 : ℕ) : ℝ)) ^ (d - 1)),
      unitProjectionBallVolume] using hv
  exact (pow_le_pow_left₀ (by positivity) hbase (d - 1)).trans hpow

/-- Exact cancellation of the projection cube and ambient cube coefficients;
no change to the original `b` or `R0` definitions. -/
theorem original_roundness_cube_coefficient {d : ℕ} (hd : 1 ≤ d) :
    (2 / (d : ℝ)) ^ (d - 1) / ((d : ℝ) * (2 * R0 d) ^ d) = 2 * b d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hR := R0_pos hd
  have hpowd : (d : ℝ) ^ d = (d : ℝ) ^ (d - 1) * d := by
    simpa only [Nat.sub_add_cancel hd] using pow_succ (d : ℝ) (d - 1)
  have hpow2 : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
    simpa only [Nat.sub_add_cancel hd] using pow_succ (2 : ℝ) (d - 1)
  simp only [b, div_pow, mul_pow, hpowd, hpow2]
  field_simp
  ring

/-- The actual geometric brightness ratio is at least the original `2*b(d)`.
Both volume estimates are proved from the actual body inclusions. -/
theorem normalized_body_directional_brightness_lower_original {d : ℕ} (hd : 2 ≤ d)
    (K : Set (Space d)) (hc : IsCompact K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (hbound : K ⊆ closedBall (0 : Space d) (R0 d))
    (u : Space d) (hu : ‖u‖ = 1) :
    2 * b d ≤ projectionVolumeSet K u / ((d : ℝ) * (volume K).toReal) := by
  let : Nontrivial (Space d) := ⟨⟨u, 0, by
    intro heq
    rw [heq, norm_zero] at hu
    exact zero_ne_one hu⟩⟩
  have hd1 : 1 ≤ d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hvol : 0 < (volume K).toReal := compact_body_volume_pos_of_unit_ball K hc hb
  have hden : 0 < (d : ℝ) * (volume K).toReal := mul_pos hdp hvol
  have hcube := bounded_body_volume_le_cube K (R0 d) (R0_pos hd1).le hbound
  have hprojection := (unit_projection_ball_volume_lower_original hd).trans
    (normalized_body_brightness_lower K hc hb u hu)
  calc
    2 * b d = (2 / (d : ℝ)) ^ (d - 1) / ((d : ℝ) * (2 * R0 d) ^ d) :=
      (original_roundness_cube_coefficient hd1).symm
    _ ≤ (2 / (d : ℝ)) ^ (d - 1) / ((d : ℝ) * (volume K).toReal) :=
      div_le_div_of_nonneg_left (by positivity) hden
        (mul_le_mul_of_nonneg_left hcube hdp.le)
    _ ≤ _ := div_le_div_of_nonneg_right hprojection hden.le

/-- Same supplied raw law, with its actual directional brightness identity.
No law, subsequence, anchors or assignment is chosen. -/
theorem normalized_convex_body_cone_directional_roundness {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d))
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hbrightness : ∀ u : Space d, ‖u‖ = 1 →
      negativeIntegral ν (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal)) :
    ∀ u : Space d, ‖u‖ = 1 →
      2 * b d ≤ negativeIntegral ν (fun x => dotProduct (fun j => u j) x) := by
  intro u hu
  rw [hbrightness u hu]
  exact normalized_body_directional_brightness_lower_original hd _ K.isCompact hb hbound u hu

/-- Raw-coordinate directional form for the assignment interface, retaining
exactly the same supplied law. -/
theorem normalized_convex_body_cone_raw_directional_roundness {d : ℕ} (hd : 2 ≤ d)
    (K : ConvexBody (Space d))
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hbrightness : ∀ u : Space d, ‖u‖ = 1 →
      negativeIntegral ν (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal)) :
    ∀ u : Fin d → ℝ, ‖WithLp.toLp 2 u‖ = 1 →
      2 * b d ≤ negativeIntegral ν (fun x => dotProduct u x) := by
  intro u hu
  exact normalized_convex_body_cone_directional_roundness hd K hb hbound ν hbrightness
    (WithLp.toLp 2 u) hu

end Entry005
