import Entry005.PyramidContinuity
import Entry005.ActualBodyHorizontalMoment

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology
namespace Entry005
variable {d : ℕ} [Nontrivial (Space d)]

theorem compact_normalized_projection_ratio_pos (K : Set (Space d))
    (hc : IsCompact K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    0 < projectionRatio K := by
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space d)
  exact normalized_projection_ratio_pos K hc hb R hR.le hbound

theorem halfspace_approximation_entryA_tendsto (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    Tendsto (fun m => entryA (halfspaceApproximationBody K hc hconv hb m))
      atTop (𝓝 (entryA K)) := by
  exact tendsto_entryA_of_dilation_sandwich K _ hc hconv
    (halfspace_approximation_body_compact K hc hconv hb)
    (fun _ => finite_halfspace_convex _ _)
    (hb (by simp)) (compact_body_volume_pos_of_unit_ball K hc hb).ne'
    (compact_normalized_projection_ratio_pos K hc hb).ne'
    halfspaceApproximationTolerance (fun m => (halfspace_approximation_tolerance_pos m).le)
    halfspace_approximation_tolerance_tendsto (subset_halfspace_approximation_body K hc hconv hb)
    (halfspace_approximation_body_subset_dilation K hc hconv hb)

/-- Both literal determinant moments converge along the same actual finite-law subsequence. -/
theorem halfspace_approximation_iid_moments_tendsto
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    Tendsto (fun k => ∫ w, |horizontalDeterminant w|
      ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) d) atTop
      (𝓝 (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)) ∧
    Tendsto (fun k => ∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)|
      ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) (d + 1)) atTop
      (𝓝 (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1))) := by
  let ν := halfspaceApproximationProbability K hc hconv hb
  let x : C(CompactConeBall d, Fin d → ℝ) := ⟨compactBallRaw, continuous_compactBallRaw⟩
  have hball : ∀ m, ∀ᵐ z ∂(ν m : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 z‖ ≤ 1 :=
    halfspace_approximation_law_ae_unit_ball K hc hconv hb
  have hmap (k : ℕ) : (compactBallLaw (ν (φ k))).map x = ν (φ k) :=
    compactBallLaw_raw_probability_pushforward _ (hball (φ k))
  have hA := tendsto_horizontal_mapped_iid_first_moment hlim x
  have hB := tendsto_lifted_mapped_iid_first_moment hlim x
  change Tendsto (fun k => ∫ w, |horizontalDeterminant w|
    ∂iidLaw ((compactBallLaw (ν (φ k))).map x : Measure (Fin d → ℝ)) d) atTop
    (𝓝 (∫ w, |horizontalDeterminant w| ∂iidLaw (μ.map x : Measure (Fin d → ℝ)) d)) at hA
  change Tendsto (fun k => ∫ w : Fin (d + 1) → Fin d → ℝ,
    |liftedDeterminant (fun j => w j.succ) (w 0)|
    ∂iidLaw ((compactBallLaw (ν (φ k))).map x : Measure (Fin d → ℝ)) (d + 1)) atTop
    (𝓝 (∫ w : Fin (d + 1) → Fin d → ℝ, |liftedDeterminant (fun j => w j.succ) (w 0)|
      ∂iidLaw (μ.map x : Measure (Fin d → ℝ)) (d + 1))) at hB
  simp_rw [hmap] at hA hB
  exact ⟨hA, hB⟩

theorem actual_body_horizontal_moment_pos_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    0 < (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) := by
  rw [actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim]
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d)))
  exact mul_pos (div_pos (by exact_mod_cast Nat.factorial_pos d)
    (pow_pos (mul_pos hd (compact_body_volume_pos_of_unit_ball K hc hb)) _))
    (normalized_projection_body_volume_pos K hc hb R hR.le hbound)

/-- The actual lifted moment is computed from actual canonical pyramid geometry,
with the finite identities passed through the same compact cone-law limit as A. -/
theorem actual_body_lifted_first_moment_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) =
      (d + 1 : ℝ) *
        (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) *
          entryA K := by
  have ht := halfspace_approximation_iid_moments_tendsto K hc hconv hb μ φ hlim
  have he := (halfspace_approximation_entryA_tendsto K hc hconv hb).comp hφ.tendsto_atTop
  have hgeo := (ht.1.const_mul (d + 1 : ℝ)).mul he
  have hid (k : ℕ) : (d + 1 : ℝ) *
      (∫ w, |horizontalDeterminant w| ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) d) *
        entryA (halfspaceApproximationBody K hc hconv hb (φ k)) =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) (d + 1)) := by
    have hfinite := finite_halfspace_entryA_lifted_moment _ _
      (halfspace_approximation_normals_unit K hc hconv hb (φ k))
      (halfspace_approximation_heights_pos K hc hconv hb (φ k))
      (halfspace_approximation_normals_injective K hc hconv hb (φ k))
      (halfspace_approximation_body_compact K hc hconv hb (φ k))
    have hA := finite_halfspace_horizontal_moment_pos _ _
      (halfspace_approximation_normals_unit K hc hconv hb (φ k))
      (halfspace_approximation_heights_pos K hc hconv hb (φ k))
      (halfspace_approximation_normals_injective K hc hconv hb (φ k))
      (halfspace_approximation_body_compact K hc hconv hb (φ k))
    change entryA (halfspaceApproximationBody K hc hconv hb (φ k)) = _ at hfinite
    rw [hfinite]
    exact mul_div_cancel₀ _ (mul_ne_zero (by positivity) hA.ne')
  simp_rw [Function.comp_def, hid] at hgeo
  exact tendsto_nhds_unique ht.2 hgeo

/-- Exact paper identity a(K)=B/((d+1)A) for a common actual compact cone-law limit. -/
theorem actual_body_entryA_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) :
    entryA K =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) /
      ((d + 1 : ℝ) *
        (∫ w, |horizontalDeterminant w| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)) := by
  rw [actual_body_lifted_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim,
    mul_div_cancel_left₀ _ (mul_ne_zero (by positivity)
      (actual_body_horizontal_moment_pos_of_compact_limit K hc hconv hb μ φ hφ hlim).ne')]

/-- Every normalized actual compact convex body has one actual centered law
satisfying brightness, the horizontal volume identity, and the canonical
pyramid identity. No law, geometric identity or weak limit is assumed. -/
theorem actual_body_cone_law_with_pyramid_first_moment
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ ν : ProbabilityMeasure (Fin d → ℝ),
      (∀ᵐ x ∂(ν : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(ν : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 → negativeIntegral (ν : Measure (Fin d → ℝ))
        (fun x => dotProduct (fun j => u j) x) =
        projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal ∧
      0 < (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) ∧
      entryA K =
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) /
        ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d)) := by
  obtain ⟨μ, φ, hφ, hlim, _, hball, hcenter, hbrightness⟩ :=
    actual_body_compact_cone_law_exists K hc hconv hb
  exact ⟨compactBallRawLaw μ, hball, hcenter, hbrightness,
    actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim,
    actual_body_horizontal_moment_pos_of_compact_limit K hc hconv hb μ φ hφ hlim,
    actual_body_entryA_of_compact_limit K hc hconv hb μ φ hφ hlim⟩

end Entry005
