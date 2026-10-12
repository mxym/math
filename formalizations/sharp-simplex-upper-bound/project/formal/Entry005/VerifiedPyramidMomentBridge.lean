import Entry005.ConditionalPyramidMomentBridge
import Entry005.ActualPyramidJointCone

/-! Consuming wrappers for the owner's actual finite-pyramid proofs.
The two exact finite obligations in the frozen assembly are now discharged.
No original source/constant/goal is changed and no measure is reselected. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology
namespace Entry005

theorem finite_actual_pyramid_volume_formula_proved (d : ℕ) :
    FiniteActualPyramidVolumeFormula d := by
  intro hd ι _ n h hn hh _hinj hc
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial (Space d) := inferInstance
  simpa only [Space, finrank_euclideanSpace_fin] using
    pyramid_finite_halfspace_volume n h hc

theorem finite_actual_pyramid_projection_formula_proved (d : ℕ) :
    FiniteActualPyramidProjectionFormula d := by
  intro hd ι _ n h hn hh hinj hc
  let : NeZero d := ⟨by omega⟩
  let : Nontrivial (Space d) := inferInstance
  have hp := pyramid_projection_body_volume_decomposition n h hn hh hinj hc
  rw [pyramid_side_zonotope_volume_lifted_moment n h hn hh hinj hc] at hp
  simpa only [Space, finrank_euclideanSpace_fin, anchorMatrix, liftedDeterminant,
    one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc] using hp

variable {d : ℕ} [Nontrivial (Space d)]

theorem actual_same_limit_anchor_moment_entryA
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) =
      ((d : ℝ) + 1) *
        (∫ base, |horizontalDeterminant base|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryA K :=
  conditional_actual_body_affine_first_moment_entryA_of_compact_limit
    (finite_actual_pyramid_volume_formula_proved d)
    (finite_actual_pyramid_projection_formula_proved d) K hc hconv hb μ φ hφ hlim

theorem actual_same_limit_anchor_defect_entryDefect
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
      (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id =
      ((d : ℝ) + 1) *
        (∫ base, |horizontalDeterminant base|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryDefect K :=
  conditional_actual_body_determinant_defect_entryDefect_of_compact_limit
    (finite_actual_pyramid_volume_formula_proved d)
    (finite_actual_pyramid_projection_formula_proved d) K hc hconv hb μ φ hφ hlim

end Entry005

