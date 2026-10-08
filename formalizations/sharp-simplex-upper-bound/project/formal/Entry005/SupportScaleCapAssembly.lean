import Entry005.FiniteMinkowskiScaleGate
import Entry005.ProjectionScaleAssembly
import Entry005.SharpConstantGates

/-! Type alignment from the SAME supplied compact limit and assignment test
to the original scale/cap constants. The finite Minkowski proposition and
actual normalized brightness facts remain explicit geometric inputs. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology

namespace Entry005

theorem actual_body_scale_of_same_assignment_budget {d n : ℕ} [Nontrivial (Space d)]
    (hMinkowski : FiniteSupportMinkowskiObligation d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hconvP : Convex ℝ P) (hKP : K ⊆ P)
    (M h : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤ h) :
    (volume P).toReal / (volume K).toReal ≤ (1 + M * h) ^ d := by
  have hscale := actual_body_assignment_volume_scale_of_finite_minkowski
    hMinkowski K hc hconv hb μ φ hφ hlim P hcP hconvP hKP M hM hbound w hw r hr
  have hcost0 : 0 ≤ ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := integral_nonneg (fun _ => norm_nonneg _)
  have hbase : 0 ≤ 1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := by positivity
  exact hscale.trans (pow_le_pow_left₀ hbase
    (by linarith [mul_le_mul_of_nonneg_left hcost hM]) d)

theorem actual_cap_of_same_assignment_and_finite_minkowski {d n : ℕ}
    [Nontrivial (Space d)] (hd : 2 ≤ d)
    (hMinkowski : FiniteSupportMinkowskiObligation d)
    (K P : ConvexBody (Space d))
    (hb : closedBall (0 : Space d) 1 ⊆ K) (hKP : K ≤ P)
    (hbound : (K : Set (Space d)) ⊆ closedBall (0 : Space d) (R0 d))
    (hPM : (P : Set (Space d)) ⊆ closedBall (0 : Space d) (M d))
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability (K : Set (Space d)) K.isCompact K.convex hb (φ k)))
      atTop (𝓝 μ))
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight (P : Set (Space d)) (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : M d * h ≤ 1)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
      ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤ h)
    (hbright : ∀ u : Space d, ‖u‖ = 1 →
      |projectionVolumeSet (P : Set (Space d)) u /
          ((d : ℝ) * (volume (P : Set (Space d))).toReal) -
        projectionVolumeSet (K : Set (Space d)) u /
          ((d : ℝ) * (volume (K : Set (Space d))).toReal)| ≤ (M d + 1) * h / 2)
    (hPbright : ∀ u : Space d, ‖u‖ = 1 →
      projectionVolumeSet (P : Set (Space d)) u /
        ((d : ℝ) * (volume (P : Set (Space d))).toReal) ≤ 1 / 2) :
    hausdorffDist (K : Set (Space d)) (P : Set (Space d)) ≤
      L d * (J d * h) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hscale := actual_body_scale_of_same_assignment_budget
    hMinkowski (K : Set (Space d)) K.isCompact K.convex hb μ φ hφ hlim
    (P : Set (Space d)) P.isCompact P.convex hKP (M d) h (M_pos hd1).le hPM w hw r hr hcost
  exact actual_cap_bound_of_scale_and_brightness hd K P hb hKP hbound hPM
    h hh hsmall hscale hbright hPbright

theorem original_local_cap_to_excess_scalar {d : ℕ} (hd : 2 ≤ d) (E delta e : ℝ)
    (he : 0 ≤ e)
    (hcap : delta ≤ L d * (J d * (Q d * (d + 1) * e)) ^
      (1 / ((d - 1 : ℕ) : ℝ)))
    (hretain : E ≤ 4 * M d * d * delta) :
    E ≤ aSharp d * e ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hM := M_pos hd1
  have hL := L_pos hd
  have hJ := J_pos hd1
  have hQ := Q_pos hd1
  have hmul := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 4 * M d * d by positivity)
  have hc : 0 ≤ J d * Q d * (d + 1) := by positivity
  have hid : J d * (Q d * (d + 1) * e) = (J d * Q d * (d + 1)) * e := by ring
  rw [hid, Real.mul_rpow hc he] at hmul
  have hfinal : 4 * M d * d * (L d *
      ((J d * Q d * (d + 1)) ^ (1 / ((d - 1 : ℕ) : ℝ)) *
        e ^ (1 / ((d - 1 : ℕ) : ℝ)))) =
      aSharp d * e ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
    unfold aSharp
    ring
  rw [hfinal] at hmul
  exact hretain.trans hmul

end Entry005
