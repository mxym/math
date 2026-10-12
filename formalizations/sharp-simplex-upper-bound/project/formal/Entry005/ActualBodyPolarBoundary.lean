import Entry005.ActualBodyHorizontalMoment
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Actual supporting-halfspace atoms lie on the fixed body's polar boundary.
This closed carrying property passes through the same compact-law weak limit. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology RealInnerProductSpace

namespace Entry005

section SupportHeight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compact_support_height_direction_nonnegative_smul
    (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (a : ℝ) (ha : 0 ≤ a) (u : E) :
    compactSupportHeight K (a • u) = a * compactSupportHeight K u := by
  apply le_antisymm
  · obtain ⟨q, hq, heq⟩ := compact_support_height_attained K hc hne (a • u)
    rw [← heq, real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (compact_support_height_bound K hc hne u q hq) ha
  · obtain ⟨q, hq, heq⟩ := compact_support_height_attained K hc hne u
    have h := compact_support_height_bound K hc hne (a • u) q hq
    simpa only [real_inner_smul_left, heq] using h

theorem continuous_compact_support_height
    (K : Set E) (hc : IsCompact K) (hne : K.Nonempty) :
    Continuous (compactSupportHeight K) := by
  obtain ⟨R, _, hR⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : E)
  have hr : ∀ q ∈ K, ‖q‖ ≤ R := by
    intro q hq
    simpa only [mem_closedBall, dist_zero_right] using hR hq
  exact (LipschitzWith.of_le_add_mul' R (fun u v => by
    simpa only [dist_eq_norm, mul_comm] using
      compact_support_height_lipschitz K hc hne R hr u v)).continuous

theorem normalized_support_height_eq_one
    (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (u : E) (hu : 0 < compactSupportHeight K u) :
    compactSupportHeight K ((compactSupportHeight K u)⁻¹ • u) = 1 := by
  rw [compact_support_height_direction_nonnegative_smul K hc hne _
    (inv_nonneg.mpr hu.le), inv_mul_cancel₀ hu.ne']

end SupportHeight

/-- The literal height-one boundary in raw Euclidean coordinates. -/
def actualPolarBoundaryRaw {d : ℕ} (K : Set (Space d)) : Set (Fin d → ℝ) :=
  {x | compactSupportHeight K (WithLp.toLp 2 x) = 1}

/-- The same fixed boundary pulled back to the actual compact unit ball. -/
def actualPolarBoundaryCompact {d : ℕ} (K : Set (Space d)) : Set (CompactConeBall d) :=
  compactBallRaw ⁻¹' actualPolarBoundaryRaw K

theorem actual_polar_boundary_raw_isClosed {d : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hne : K.Nonempty) :
    IsClosed (actualPolarBoundaryRaw K) :=
  isClosed_eq ((continuous_compact_support_height K hc hne).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))) continuous_const

theorem actual_polar_boundary_compact_isClosed {d : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hne : K.Nonempty) :
    IsClosed (actualPolarBoundaryCompact K) :=
  (actual_polar_boundary_raw_isClosed K hc hne).preimage continuous_compactBallRaw

theorem halfspace_approximation_atom_polar_boundary {d : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ)
    (i : halfspaceApproximationNormals K hc hconv hb m) :
    finiteConePoint
      (fun u : halfspaceApproximationNormals K hc hconv hb m => fun j => (u : Space d) j)
      (fun u => compactSupportHeight K (u : Space d)) i ∈ actualPolarBoundaryRaw K := by
  have hne : K.Nonempty := ⟨0, hb (by simp)⟩
  have heq : WithLp.toLp 2 (finiteConePoint
      (fun u : halfspaceApproximationNormals K hc hconv hb m => fun j => (u : Space d) j)
      (fun u => compactSupportHeight K (u : Space d)) i) =
        (compactSupportHeight K (i : Space d))⁻¹ • (i : Space d) := by
    ext j
    simp [finiteConePoint, div_eq_mul_inv, mul_comm]
  change compactSupportHeight K _ = 1
  rw [heq]
  exact normalized_support_height_eq_one K hc hne (i : Space d)
    (halfspace_approximation_heights_pos K hc hconv hb m i)

theorem halfspace_approximation_law_ae_polar_boundary {d : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ∀ᵐ x ∂halfspaceApproximationLaw K hc hconv hb m,
      x ∈ actualPolarBoundaryRaw K := by
  have hne : K.Nonempty := ⟨0, hb (by simp)⟩
  apply Measure.ae_sum_iff.mpr
  intro i
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff (actual_polar_boundary_raw_isClosed K hc hne).measurableSet).mpr
    (halfspace_approximation_atom_polar_boundary K hc hconv hb m i)

theorem probability_closed_carried_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (ν : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (hlim : Tendsto ν atTop (𝓝 μ))
    (C : Set Ω) (hC : IsClosed C) (hcarry : ∀ k, ∀ᵐ x ∂(ν k : Measure Ω), x ∈ C) :
    ∀ᵐ x ∂(μ : Measure Ω), x ∈ C := by
  have heq (k : ℕ) : (ν k : Measure Ω) C = 1 :=
    (mem_ae_iff_prob_eq_one hC.measurableSet).mp (hcarry k)
  have hl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hC
  simp_rw [heq] at hl
  have hfull : (μ : Measure Ω) C = 1 :=
    le_antisymm prob_le_one (by simpa only [limsup_const] using hl)
  exact (mem_ae_iff_prob_eq_one hC.measurableSet).mpr hfull

section ActualLimit

variable {d : ℕ} [Nontrivial (Space d)]

theorem halfspace_approximation_compact_law_ae_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    ∀ᵐ z ∂(compactBallLaw (halfspaceApproximationProbability K hc hconv hb m) :
      Measure (CompactConeBall d)), z ∈ actualPolarBoundaryCompact K := by
  have hball := halfspace_approximation_law_ae_unit_ball K hc hconv hb m
  have hraw := halfspace_approximation_law_ae_polar_boundary K hc hconv hb m
  change ∀ᵐ x ∂(halfspaceApproximationProbability K hc hconv hb m :
    Measure (Fin d → ℝ)), x ∈ actualPolarBoundaryRaw K at hraw
  rw [← compactBallLaw_raw_pushforward
    (halfspaceApproximationProbability K hc hconv hb m) hball] at hraw
  exact ae_of_ae_map measurable_compactBallRaw.aemeasurable hraw

/-- Closed carrying passes along the displayed actual weak limit, with no
replacement measure or replacement subsequence. -/
theorem actual_body_compact_limit_ae_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    ∀ᵐ z ∂(μ : Measure (CompactConeBall d)), z ∈ actualPolarBoundaryCompact K := by
  exact probability_closed_carried_of_tendsto _ μ hlim _
    (actual_polar_boundary_compact_isClosed K hc ⟨0, hb (by simp)⟩)
    (fun k => halfspace_approximation_compact_law_ae_polar_boundary K hc hconv hb (φ k))

theorem actual_body_compact_limit_raw_ae_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    ∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), x ∈ actualPolarBoundaryRaw K := by
  rw [compactBallRawLaw, ProbabilityMeasure.toMeasure_map]
  exact (ae_map_iff measurable_compactBallRaw.aemeasurable
    (actual_polar_boundary_raw_isClosed K hc ⟨0, hb (by simp)⟩).measurableSet).mpr
      (actual_body_compact_limit_ae_polar_boundary K hc hconv hb μ φ hlim)

theorem actual_body_compact_limit_support_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ⊆ actualPolarBoundaryRaw K :=
  Measure.support_subset_of_isClosed
    (actual_polar_boundary_raw_isClosed K hc ⟨0, hb (by simp)⟩)
    (actual_body_compact_limit_raw_ae_polar_boundary K hc hconv hb μ φ hlim)

theorem actual_body_compact_limit_compact_support_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    (μ : Measure (CompactConeBall d)).support ⊆ actualPolarBoundaryCompact K :=
  Measure.support_subset_of_isClosed
    (actual_polar_boundary_compact_isClosed K hc ⟨0, hb (by simp)⟩)
    (actual_body_compact_limit_ae_polar_boundary K hc hconv hb μ φ hlim)

/-- The actual body's constructed law simultaneously has brightness, the
horizontal first moment, and polar-boundary support. No support or limiting-law
premise is supplied, and all conclusions concern the same compact law and subsequence. -/
theorem actual_body_compact_cone_law_exists_with_polar_boundary
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ μ : ProbabilityMeasure (CompactConeBall d), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
        atTop (𝓝 μ) ∧
      Tendsto (fun k => halfspaceApproximationProbability K hc hconv hb (φ k))
        atTop (𝓝 (compactBallRawLaw μ)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 →
        negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
          (fun x => dotProduct (fun j => u j) x) =
          projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), x ∈ actualPolarBoundaryRaw K) ∧
      (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ⊆ actualPolarBoundaryRaw K ∧
      (∫ base, |horizontalDeterminant base|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal := by
  obtain ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness⟩ :=
    actual_body_compact_cone_law_exists K hc hconv hb
  exact ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness,
    actual_body_compact_limit_raw_ae_polar_boundary K hc hconv hb μ φ hlim,
    actual_body_compact_limit_support_polar_boundary K hc hconv hb μ φ hlim,
    actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim⟩

end ActualLimit

end Entry005
