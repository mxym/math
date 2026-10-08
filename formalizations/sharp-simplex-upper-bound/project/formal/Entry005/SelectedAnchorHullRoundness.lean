import Entry005.UnitBallAnchorChain
import Entry005.Cap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section
open MeasureTheory Metric
open scoped BigOperators RealInnerProductSpace

namespace Entry005

theorem euclidean_inner_raw {d : ℕ} (u : EuclideanSpace ℝ (Fin d))
    (x : Fin d → ℝ) :
    inner ℝ u (WithLp.toLp 2 x) = dotProduct u x := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- Small integrated assignment error transfers directional first moments to an
actual ball in the convex hull of the selected anchors. -/
theorem selected_anchor_ball_subset_convexHull {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (r : (Fin d → ℝ) → Fin (d + 1))
    {b : ℝ} (hb : 0 < b)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u x))
    (herror : Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖) ν)
    (herr : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤ b) :
    closedBall (0 : EuclideanSpace ℝ (Fin d)) b ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))) := by
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i)))
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  have hcomp : IsCompact K := (Set.finite_range _).isCompact_convexHull ℝ
  have hne : K.Nonempty := ⟨WithLp.toLp 2 (w 0),
    subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
  intro q hq
  by_contra hqK
  obtain ⟨k, hk, u, hdist, hu, hgap, hsep, _⟩ :=
    closest_support K hconv hcomp.isComplete hne q hqK
  have hqnorm : ‖q‖ ≤ b := by simpa only [mem_closedBall, dist_zero_right] using hq
  have hqproj : inner ℝ u q ≤ b := by
    have h := real_inner_le_norm u q
    rw [hu, one_mul] at h
    exact h.trans hqnorm
  have hkproj : inner ℝ u k < b := by linarith
  have hdot : Integrable (fun x : Fin d → ℝ => dotProduct u x) ν :=
    integrable_finsetSum _ (fun i _ => (hX i).const_mul _)
  have hposint : Integrable (fun x : Fin d → ℝ => max (dotProduct u x) 0) ν :=
    hdot.pos_part
  have hpos : 2 * b ≤ ∫ x : Fin d → ℝ, max (dotProduct u x) 0 ∂ν := by
    have h := hround (-u) (by simpa only [norm_neg] using hu)
    simpa [negativeIntegral, dotProduct, Finset.sum_neg_distrib] using h
  have hpoint : ∀ x : Fin d → ℝ, max (dotProduct u x) 0 ≤
      max (inner ℝ u k) 0 + ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ := by
    intro x
    have hwK : WithLp.toLp 2 (w (r x)) ∈ K :=
      subset_convexHull ℝ _ (Set.mem_range_self (r x))
    have hanchor := hsep _ hwK
    have hdiff := real_inner_le_norm u
      (WithLp.toLp 2 x - WithLp.toLp 2 (w (r x)))
    rw [hu, one_mul, inner_sub_right, euclidean_inner_raw] at hdiff
    apply max_le
    · linarith [le_max_left (inner ℝ u k) 0]
    · exact add_nonneg (le_max_right _ _) (norm_nonneg _)
  have hupper : (∫ x : Fin d → ℝ, max (dotProduct u x) 0 ∂ν) ≤
      max (inner ℝ u k) 0 + b := by
    calc
      (∫ x : Fin d → ℝ, max (dotProduct u x) 0 ∂ν) ≤
          ∫ x, max (inner ℝ u k) 0 +
            ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν :=
        integral_mono hposint ((integrable_const _).add herror) hpoint
      _ = max (inner ℝ u k) 0 +
          ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν := by
        rw [integral_add (integrable_const _) herror]
        simp
      _ ≤ max (inner ℝ u k) 0 + b := add_le_add_right herr _
  have hmax : max (inner ℝ u k) 0 < b := max_lt hkproj hb
  linarith

/-- Unit-ball support and measurable assignment give all integrability needed
for the selected-anchor hull roundness theorem. -/
theorem unit_ball_selected_anchor_ball_subset_convexHull {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (r : (Fin d → ℝ) → Fin (d + 1)) (hr : Measurable r)
    {b : ℝ} (hb : 0 < b)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u x))
    (herr : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤ b) :
    closedBall (0 : EuclideanSpace ℝ (Fin d)) b ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))) := by
  have hmX : Measurable (fun x : Fin d → ℝ => WithLp.toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
  have hmw : Measurable (fun x => WithLp.toLp 2 (w (r x))) :=
    (measurable_of_finite (fun i => WithLp.toLp 2 (w i))).comp hr
  have hint : Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖) ν := by
    apply (integrable_const (2 : ℝ)).mono' (hmX.sub hmw).norm.aestronglyMeasurable
    filter_upwards [hball] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by linarith [hw (r x)])
  exact selected_anchor_ball_subset_convexHull ν
    (unit_ball_coordinate_integrable ν hball) w r hb hround hint herr

end Entry005
