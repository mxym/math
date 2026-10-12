import Entry005.PyramidEntryDefect

/- Exact narrow reuse of the main owner iid moment helpers; bodies unchanged.
Original IidWeightedAnchorSelection.lean SHA256: 2ea69f9c469ccb5123d99f755d405cd4103276fa8811eac5dc23e5ffd3b0861d. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Entry005.PyramidIidMomentReuse

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

end Entry005.PyramidIidMomentReuse
