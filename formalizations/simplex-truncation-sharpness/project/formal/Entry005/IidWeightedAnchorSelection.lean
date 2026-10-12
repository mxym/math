import Entry005.PaperWitnessTransport
import Entry005.RoundAnchorChain
import Entry005.WeightedAnchorSelection
import Entry005.UnitBallAnchorChain

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem measurable_iid_anchor_volume {d : ℕ} :
    Measurable (fun w : Fin (d + 1) → Fin d → ℝ => |(anchorMatrix w).det|) := by
  have hd : Measurable (fun w : Fin (d + 1) → Fin d → ℝ =>
      liftedDeterminant (fun i => w i.succ) (w 0)) := measurable_lifted_determinant
    (fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i.succ))
    (fun i => (measurable_pi_apply i).comp (measurable_pi_apply 0))
  simpa only [anchorMatrix, liftedDeterminant, Real.norm_eq_abs] using hd.norm

theorem iid_anchor_volume_integrable {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν) :
    Integrable (fun w : Fin (d + 1) → Fin d → ℝ => |(anchorMatrix w).det|)
      (iidLaw ν (d + 1)) := by
  have hXLift (i : Fin (d + 1)) :
      Integrable (fun x : Fin d → ℝ => liftedCoordinates id x i) ν := by
    induction i using Fin.cases with
    | zero => simp [liftedCoordinates]
    | succ i => simpa [liftedCoordinates] using hX i
  have hmatrix (w : Fin (d + 1) → Fin d → ℝ) :
      sampledMatrix (liftedCoordinates id) w = anchorMatrix w := by
    ext i j
    simp [sampledMatrix, anchor_matrix_entry, liftedCoordinates]
  simpa only [hmatrix, Real.norm_eq_abs] using
    (sampled_determinant_integrable (liftedCoordinates id) hXLift).norm

/-- The actual iid anchor law tilted by normalized absolute determinant. -/
def iidAnchorVolumeWeightedLaw {d : ℕ} (ν : Measure (Fin d → ℝ)) :
    Measure (Fin (d + 1) → Fin d → ℝ) :=
  volumeWeightedLaw (iidLaw ν (d + 1)) (fun w => |(anchorMatrix w).det|)

theorem iid_anchor_volume_weighted_law_probability {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    IsProbabilityMeasure (iidAnchorVolumeWeightedLaw ν) :=
  volume_weighted_law_probability (iidLaw ν (d + 1)) measurable_iid_anchor_volume
    (iid_anchor_volume_integrable ν hX) (fun w => abs_nonneg (anchorMatrix w).det) hB

theorem iid_anchor_support_ae {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1), ∀ i, w i ∈ ν.support := by
  apply ae_all_iff.2
  intro i
  exact (measurePreserving_eval (fun _ : Fin (d + 1) => ν) i).quasiMeasurePreserving.ae
    ν.support_mem_ae

theorem iid_anchor_volume_weighted_law_ae_support_pos {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    ∀ᵐ w ∂iidAnchorVolumeWeightedLaw ν,
      (∀ i, w i ∈ ν.support) ∧ 0 < |(anchorMatrix w).det| :=
  volume_weighted_law_ae_good (iidLaw ν (d + 1)) measurable_iid_anchor_volume hB
    (iid_anchor_support_ae ν)

/-- The anchor-volume first moment is the actual base-and-test determinant moment. -/
theorem iid_anchor_volume_integral_eq {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) =
      ∫ z : (Fin d → Fin d → ℝ) × (Fin d → ℝ),
        |liftedDeterminant z.1 z.2| ∂(iidLaw ν d).prod ν := by
  let e : (Fin (d + 1) → Fin d → ℝ) ≃ᵐ
      ((Fin d → Fin d → ℝ) × (Fin d → ℝ)) :=
    (iidSplit d).trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (iidLaw ν (d + 1)) ((iidLaw ν d).prod ν) :=
    Measure.measurePreserving_swap.comp (iid_split_preserving ν d)
  have heval (w : Fin (d + 1) → Fin d → ℝ) :
      e w = (fun i => w i.succ, w 0) := by
    ext i <;> simp [e, iidSplit, MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.tail, MeasurableEquiv.prodComm]
  simpa only [heval, anchorMatrix, liftedDeterminant] using
    he.integral_comp' (fun z => |liftedDeterminant z.1 z.2|)

/-- The actual integrated assignment witness has the exact paper-index budget. -/
theorem iid_paper_assignment_witness_budget {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0) :
    Integrable (fun w => ∫ x, determinantAssignmentWitness w x ∂ν)
        (iidLaw ν (d + 1)) ∧
      (∀ w, 0 ≤ ∫ x, determinantAssignmentWitness w x ∂ν) ∧
      (∫ w, ∫ x, determinantAssignmentWitness w x ∂ν ∂iidLaw ν (d + 1)) ≤
        (((d : ℝ) + 1) * ((d : ℝ) + 2) / 2) *
          determinantLawDefect (iidLaw ν d) ν id id := by
  have hmF : Measurable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) =>
      liftedDeterminant z.1 z.2) := measurable_lifted_determinant
    (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)
  have hF := iid_lifted_determinant_integrable id hX
  have hfiber := fun base : Fin d → Fin d → ℝ => lifted_determinant_integrable base hX
  obtain ⟨hiH, hH0, hbudget⟩ := transported_witness_budget hmF hF hfiber
    (fun i : PaperWitnessIndex d => iidWitnessTransport d (paperWitnessPermutation d i))
    (paper_witness_transport_preserving ν)
  have hid : familyDefect (iidLaw ν d) ν (fun base x => liftedDeterminant base x) =
      determinantLawDefect (iidLaw ν d) ν id id := by
    simp only [familyDefect, determinantLawDefect, integral_lifted_determinant _ hX hcenter,
      id_eq]
  rw [hid, paper_witness_index_card_real] at hbudget
  simpa only [integral_determinant_assignment_witness_eq_transportedWitnessSum] using
    And.intro hiH (And.intro hH0 hbudget)

/-- The witness-to-volume ratio is integrable under the actual volume tilt,
and its tilted mean has the exact first-moment paper budget. -/
theorem iid_anchor_volume_weighted_witness_ratio_budget {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    Integrable (fun w => (∫ x, determinantAssignmentWitness w x ∂ν) /
        |(anchorMatrix w).det|) (iidAnchorVolumeWeightedLaw ν) ∧
      (∫ w, (∫ x, determinantAssignmentWitness w x ∂ν) /
        |(anchorMatrix w).det| ∂iidAnchorVolumeWeightedLaw ν) ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2) / 2) *
          determinantLawDefect (iidLaw ν d) ν id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw ν (d + 1)) := by
  obtain ⟨hiH, hH0, hbudget⟩ := iid_paper_assignment_witness_budget ν hX hcenter
  refine ⟨volume_weighted_ratio_integrable (iidLaw ν (d + 1)) measurable_iid_anchor_volume
    (fun w => abs_nonneg (anchorMatrix w).det) hiH hB, ?_⟩
  exact (volume_weighted_ratio_integral_le (iidLaw ν (d + 1)) measurable_iid_anchor_volume
    (fun w => abs_nonneg (anchorMatrix w).det) hiH hH0 hB).trans
      (div_le_div_of_nonneg_right hbudget hB.le)

/-- Volume-weighted selection attains the sharp first-moment witness-to-volume
ratio at actual support anchors of the iid law. -/
theorem iid_volume_weighted_paper_witness_anchor {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support) ∧ 0 < |(anchorMatrix w).det| ∧
      (∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det| ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2) / 2) *
          determinantLawDefect (iidLaw ν d) ν id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw ν (d + 1)) := by
  obtain ⟨hiH, hH0, hbudget⟩ := iid_paper_assignment_witness_budget ν hX hcenter
  exact volume_weighted_selection (iidLaw ν (d + 1)) measurable_iid_anchor_volume
    (iid_anchor_volume_integrable ν hX) (fun w => abs_nonneg (anchorMatrix w).det)
    hiH hH0 (iid_anchor_support_ae ν) hB hbudget

/-- Unit-ball support yields selected unit anchors with the same exact
volume-weighted witness ratio. -/
theorem unit_ball_volume_weighted_paper_witness_anchor {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hB : 0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1)) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      0 < |(anchorMatrix w).det| ∧
      (∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det| ≤
        ((((d : ℝ) + 1) * ((d : ℝ) + 2) / 2) *
          determinantLawDefect (iidLaw ν d) ν id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw ν (d + 1)) := by
  obtain ⟨w, hsupp, hV, hratio⟩ := iid_volume_weighted_paper_witness_anchor ν
    (unit_ball_coordinate_integrable ν hball) hcenter hB
  exact ⟨w, fun i => ⟨hsupp i, unit_ball_support_bound ν hball (w i) (hsupp i)⟩,
    hV, hratio⟩

end Entry005
