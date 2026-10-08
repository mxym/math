import Entry005.ActualPyramidMoment

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology
namespace Entry005

/-- The actual product-law defect is exactly the difference of the literal iid moments. -/
theorem determinantLawDefect_iid_eq {d : ℕ} (ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure ν] :
    determinantLawDefect (iidLaw ν d) ν id id =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) -
      (∫ w, |horizontalDeterminant w| ∂iidLaw ν d) := by
  have hB := PyramidIidMomentReuse.iid_anchor_volume_integral_eq ν
  change (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) =
    (∫ z : (Fin d → Fin d → ℝ) × (Fin d → ℝ),
      |liftedDeterminant z.1 z.2| ∂(iidLaw ν d).prod ν) at hB
  unfold determinantLawDefect
  simp only [id_eq, ← hB]

/-- Exact defect algebra for a law whose two literal moments compute the actual invariant. -/
theorem entryDefect_iid_moment_identity {d : ℕ} (K : Set (Space d))
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hA : 0 < (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))
    (hentry : entryA K =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) /
      ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))) :
    determinantLawDefect (iidLaw ν d) ν id id =
      (d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw ν d) * entryDefect K := by
  rw [determinantLawDefect_iid_eq]
  unfold entryDefect
  rw [hentry]
  simp only [finrank_euclideanSpace_fin]
  field_simp [hA.ne']

theorem entryDefect_iid_nonnegative {d : ℕ} (K : Set (Space d))
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hA : 0 < (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))
    (hentry : entryA K =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) /
      ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))) :
    0 ≤ entryDefect K := by
  have hD := centered_iid_lifted_moment_ge_horizontal ν hX hcenter
  have he := entryDefect_iid_moment_identity K ν hA hentry
  rw [determinantLawDefect_iid_eq] at he
  have hp : 0 < (d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw ν d) :=
    mul_pos (by positivity) hA
  exact (mul_nonneg_iff_of_pos_left hp).mp (by linarith [he])

theorem entryDefect_iid_defect_ratio {d : ℕ} (K : Set (Space d))
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hA : 0 < (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))
    (hentry : entryA K =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) /
      ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw ν d))) :
    determinantLawDefect (iidLaw ν d) ν id id /
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) =
      (d + 1 : ℝ) * entryDefect K / (1 + (d + 1 : ℝ) * entryDefect K) := by
  have hD := entryDefect_iid_moment_identity K ν hA hentry
  have hB := hA.trans_le (centered_iid_lifted_moment_ge_horizontal ν hX hcenter)
  have he := entryDefect_iid_nonnegative K ν hX hcenter hA hentry
  have hp : 0 < 1 + (d + 1 : ℝ) * entryDefect K := by positivity
  rw [determinantLawDefect_iid_eq] at hD ⊢
  field_simp [hB.ne', hp.ne']
  nlinarith [hD]

variable {d : ℕ} [Nontrivial (Space d)]

/-- Every normalized actual body has a single centered law satisfying all
cone brightness and actual pyramid identities, including D=(d+1)A e(K). -/
theorem actual_body_cone_law_with_pyramid_defect
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
        ((d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d)) ∧
      determinantLawDefect (iidLaw (ν : Measure (Fin d → ℝ)) d) (ν : Measure (Fin d → ℝ)) id id =
        (d + 1 : ℝ) * (∫ w, |horizontalDeterminant w| ∂iidLaw (ν : Measure (Fin d → ℝ)) d) * entryDefect K ∧
      determinantLawDefect (iidLaw (ν : Measure (Fin d → ℝ)) d) (ν : Measure (Fin d → ℝ)) id id /
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (ν : Measure (Fin d → ℝ)) (d + 1)) =
        (d + 1 : ℝ) * entryDefect K / (1 + (d + 1 : ℝ) * entryDefect K) := by
  obtain ⟨ν, hball, hcenter, hbright, hhorizontal, hA, hentry⟩ :=
    actual_body_cone_law_with_pyramid_first_moment K hc hconv hb
  exact ⟨ν, hball, hcenter, hbright, hhorizontal, hA, hentry,
    entryDefect_iid_moment_identity K _ hA hentry,
    entryDefect_iid_defect_ratio K _ (unit_ball_coordinate_integrable _ hball) hcenter hA hentry⟩

/-- The normalized actual body's canonical pyramid defect is nonnegative. -/
theorem actual_body_entryDefect_nonnegative (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) : 0 ≤ entryDefect K := by
  obtain ⟨ν, hball, hcenter, _, _, hA, hentry⟩ :=
    actual_body_cone_law_with_pyramid_first_moment K hc hconv hb
  exact entryDefect_iid_nonnegative K _ (unit_ball_coordinate_integrable _ hball) hcenter hA hentry

end Entry005
