import Entry005.FiniteRadialSupportScale
import Entry005.SameWitnessOriginalQBudget

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology
namespace Entry005

theorem original_Q_absorbs_radial_power {d : ℕ} (hd : 1 ≤ d) :
    M d ^ (d - 1) * ((d + 1 : ℝ) * (d + 2 : ℝ)) ≤ Q d := by
  have hp := pow_le_pow_right₀ (original_one_le_M hd) (show d - 1 ≤ 4 * d by omega)
  have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hpow : M d ^ (d - 1) ≤ (8 : ℝ) ^ d * M d ^ (4 * d) :=
    hp.trans (by nlinarith [pow_nonneg (M_pos hd).le (4 * d)])
  have he := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ (d + 1 : ℝ) * (d + 2 : ℝ) by positivity)
  simpa only [Q, mul_assoc, mul_comm, mul_left_comm] using he

theorem original_radial_strong_cost_absorption {d : ℕ} (hd : 1 ≤ d)
    (e cost : ℝ) (he : 0 ≤ e)
    (hcost : cost ≤ ((d + 1 : ℝ) * (d + 2 : ℝ)) *
      ((d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e))) :
    M d ^ (d - 1) * cost ≤ Q d * (d + 1) * e := by
  let t : ℝ := (d + 1 : ℝ) * e
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ t / (1 + t) := by positivity
  have hrt : t / (1 + t) ≤ t := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  calc
    _ ≤ M d ^ (d - 1) * (((d + 1 : ℝ) * (d + 2 : ℝ)) * (t / (1 + t))) :=
      mul_le_mul_of_nonneg_left hcost (pow_nonneg (M_pos hd).le _)
    _ = (M d ^ (d - 1) * ((d + 1 : ℝ) * (d + 2 : ℝ))) * (t / (1 + t)) := by ring
    _ ≤ Q d * (t / (1 + t)) :=
      mul_le_mul_of_nonneg_right (original_Q_absorbs_radial_power hd) hr
    _ ≤ Q d * t := mul_le_mul_of_nonneg_left hrt (Q_pos hd).le
    _ = _ := by dsimp [t]; ring

/-- The original scale premise follows directly from actual radial cones and
the strong SAME-assignment bound. No finite Minkowski obligation remains. -/
theorem actual_body_original_scale_of_strong_same_assignment {d n : ℕ}
    [Nontrivial (Space d)] (hd : 1 ≤ d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hKP : K ⊆ P)
    (hPM : P ⊆ closedBall (0 : Space d) (M d))
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r)
    (e : ℝ) (he : 0 ≤ e)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
      ((d + 1 : ℝ) * (d + 2 : ℝ)) *
        ((d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e))) :
    (volume P).toReal / (volume K).toReal ≤
      (1 + M d * (Q d * (d + 1) * e)) ^ d := by
  have hlinear := actual_body_same_assignment_linear_volume_bound hd K hc hconv hb μ φ hφ hlim
    P hcP hKP (M d) (original_one_le_M hd) hPM w hw r hr
  have habs := original_radial_strong_cost_absorption hd e _ he hcost
  have hmul := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (d : ℝ) * M d by have := M_pos hd; positivity)
  have hpow : M d ^ d = M d * M d ^ (d - 1) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hbound : (volume P).toReal / (volume K).toReal ≤
      1 + (d : ℝ) * (M d * (Q d * (d + 1) * e)) := by
    rw [hpow] at hlinear
    nlinarith
  have hnonneg : 0 ≤ M d * (Q d * (d + 1) * e) := by
    have := M_pos hd
    have := Q_pos hd
    positivity
  exact hbound.trans (one_add_mul_le_pow (by linarith) d)

end Entry005
