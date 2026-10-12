import Entry005.CovarianceConditioning

/-! Direction roundness to actual iid support anchors and their witness budget.
No event probability, second moment, or coordinate-law transport is assumed.
The upper determinant bound remains explicit; the original paper uses C=2^d.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem iid_lifted_determinant_integrable {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {d : ℕ} (X : α → Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν) :
    Integrable (fun z : (Fin d → α) × α =>
      liftedDeterminant (fun i => X (z.1 i)) (X z.2)) ((iidLaw ν d).prod ν) := by
  let e : (Fin (d + 1) → α) ≃ᵐ ((Fin d → α) × α) :=
    (iidSplit d).trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (iidLaw ν (d + 1)) ((iidLaw ν d).prod ν) :=
    Measure.measurePreserving_swap.comp (iid_split_preserving ν d)
  have hXLift (i : Fin (d + 1)) : Integrable (fun x => liftedCoordinates X x i) ν := by
    induction i using Fin.cases with
    | zero => simp [liftedCoordinates]
    | succ i => simpa [liftedCoordinates] using hX i
  have h := he.symm.integrable_comp_of_integrable (sampled_determinant_integrable _ hXLift)
  have hmatrix (z : (Fin d → α) × α) :
      sampledMatrix (liftedCoordinates X) (e.symm z) =
        witnessMatrix (fun i => X (z.1 i)) (X z.2) := by
    ext i j
    induction j using Fin.cases <;>
      simp [e, iidSplit, sampledMatrix, liftedCoordinates, witnessMatrix] <;> rfl
  simpa only [Function.comp_def, hmatrix, liftedDeterminant] using h

theorem round_iid_witness_anchor {d : ℕ} (hd : 1 ≤ d) {ι : Type*} [Fintype ι]
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    (hpair : ∀ i j, Integrable (fun x : Fin d → ℝ => x i * x j) ν)
    {b C : ℝ} (hb : 0 < b) (hC : 0 < C)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u x))
    (p : ι → Equiv.Perm (Fin (d + 2)))
    (hbound : ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1),
      |liftedDeterminant (fun i => w i.succ) (w 0)| ≤ C) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support) ∧
      b ^ d ≤ |liftedDeterminant (fun i => w i.succ) (w 0)| ∧
      transportedWitnessSum ν (fun base x => liftedDeterminant base x)
        (fun i => iidWitnessTransport d (p i)) w ≤
        ((Fintype.card ι : ℝ) * determinantLawDefect (iidLaw ν d) ν id id) * C ^ 2 / (b ^ d) ^ 2 := by
  exact iid_determinant_witness_anchor ν hX hcenter
    (iid_lifted_determinant_integrable id hX) p (pow_pos hb d) hC hbound
    (round_lifted_second_moment_lower hd id hX hcenter hpair hb.le hround)

end Entry005
