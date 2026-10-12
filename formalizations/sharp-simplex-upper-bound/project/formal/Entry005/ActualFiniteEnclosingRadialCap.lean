import Entry005.FiniteHalfspaceCenteredCorrection
import Entry005.SupportScaleCapAssembly
import Entry005.OriginalRadialScale

/-! Actual enclosing-simplex cap with direct radial scale and the strong SAME-law cost.
No finite Minkowski or first-variation premise remains. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology

namespace Entry005

theorem actual_finite_enclosing_body_strong_same_assignment_cap {d : ℕ}
    [Nontrivial (Space d)] (hd : 2 ≤ d)
    (K P : ConvexBody (Space d))
    (hb : closedBall (0 : Space d) 1 ⊆ K) (hKP : K ≤ P)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (hPM : (P : Set (Space d)) ⊆ closedBall (0 : Space d) (M d))
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability (K : Set (Space d)) K.isCompact K.convex hb (φ k)))
      atTop (𝓝 μ))
    (hcenter : ∀ j, (∫ x, x j ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) = 0)
    (hKbrightness : ∀ u : Space d, ‖u‖ = 1 →
      negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
        (fun x => dotProduct u x) =
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal))
    (n : Fin (d + 1) → Space d) (heights : Fin (d + 1) → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < heights i) (hinj : Function.Injective n)
    (hP : (P : Set (Space d)) = finiteHalfspaceSet n heights)
    (w : Fin (d + 1) → Fin d → ℝ)
    (hatom : ∀ i, finiteConePoint (fun i j => n i j) heights i = w i)
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (ha : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)))
    (hround : closedBall (0 : Space d) (b d) ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i))))
    (hsupport : ∀ i, compactSupportHeight (P : Set (Space d)) (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (d + 1)) (hr : Measurable r)
    (e : ℝ) (he : 0 ≤ e) (hesmall : e ≤ eSharp d)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
      ((d + 1 : ℝ) * (d + 2 : ℝ)) *
        ((d + 1 : ℝ) * e / (1 + (d + 1 : ℝ) * e))) :
    hausdorffDist (K : Set (Space d)) (P : Set (Space d)) ≤
      L d * (J d * (Q d * (d + 1) * e)) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  let h : ℝ := Q d * (d + 1) * e
  have hherror : 0 ≤ h := by dsimp [h]; have := Q_pos hd1; positivity
  have hsmall : M d * h ≤ 1 := original_small_error_implies_M_budget hd1 e hesmall
  have hcostQ := hcost.trans (strong_ratio_assignment_le_original_Q_budget hd1 e he)
  have hdim : finrank ℝ (Space d) = d := by simp [Space]
  have hcF : IsCompact (finiteHalfspaceSet n heights) := by rw [← hP]; exact P.isCompact
  have hbright0 := finite_halfspace_centered_assignment_brightness
    (compactBallRawLaw μ : Measure (Fin d → ℝ)) (compactBallRawLaw_ae_unit_ball μ) hcenter
    n heights w hn hh hinj hcF hatom hw ha r hr (b d) h (b_pos hd1) hherror hcostQ hround
  have hbright : ∀ u : Space d, ‖u‖ = 1 →
      |projectionVolumeSet (P : Set (Space d)) u /
          ((d : ℝ) * (volume (P : Set (Space d))).toReal) -
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal)| ≤ (M d + 1) * h / 2 := by
    intro u hu
    have hx := hbright0 u hu
    rw [hKbrightness u hu, ← hP, hdim] at hx
    simpa only [M, one_div] using hx
  have hPbright : ∀ u : Space d, ‖u‖ = 1 →
      projectionVolumeSet (P : Set (Space d)) u /
        ((d : ℝ) * (volume (P : Set (Space d))).toReal) ≤ 1 / 2 := by
    intro u hu
    have hx := finite_halfspace_unit_atom_normalized_brightness_le_half
      n heights w hn hh hinj hcF hatom hw u hu
    rwa [← hP, hdim] at hx
  have hscale := actual_body_original_scale_of_strong_same_assignment hd1
    (K : Set (Space d)) K.isCompact K.convex hb μ φ hφ hlim
    (P : Set (Space d)) P.isCompact hKP hPM w hsupport r hr e he hcost
  exact actual_cap_bound_of_scale_and_brightness hd K P hb hKP hbound hPM
    h hherror hsmall hscale hbright hPbright

end Entry005
