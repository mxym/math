import Entry005.PyramidIidMomentReuse

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005

/-- Genuine centered iid Jensen cancellation; coordinates need only first moments. -/
theorem centered_iid_lifted_moment_ge_horizontal {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0) :
    (∫ w : Fin d → Fin d → ℝ, |horizontalDeterminant w| ∂iidLaw ν d) ≤
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) := by
  let e : (Fin (d + 1) → Fin d → ℝ) ≃ᵐ ((Fin d → Fin d → ℝ) × (Fin d → ℝ)) :=
    (iidSplit d).trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (iidLaw ν (d + 1)) ((iidLaw ν d).prod ν) :=
    Measure.measurePreserving_swap.comp (iid_split_preserving ν d)
  have heval (w : Fin (d + 1) → Fin d → ℝ) : e w = (fun i => w i.succ, w 0) := by
    ext i <;> simp [e, iidSplit, MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.tail, MeasurableEquiv.prodComm]
  have hmF : Measurable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) => liftedDeterminant z.1 z.2) :=
    measurable_lifted_determinant
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  have habs : Integrable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) =>
      |liftedDeterminant z.1 z.2|) ((iidLaw ν d).prod ν) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    simpa only [Function.comp_def, heval, anchorMatrix, liftedDeterminant] using
      PyramidIidMomentReuse.iid_anchor_volume_integrable ν hX
  have hF : Integrable (fun z : (Fin d → Fin d → ℝ) × (Fin d → ℝ) =>
      liftedDeterminant z.1 z.2) ((iidLaw ν d).prod ν) := by
    apply (integrable_norm_iff hmF.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using habs
  have hD := (centered_determinant_family_budget (σ := iidLaw ν d) (base := id) (X := id)
    hX hcenter hmF hF).1
  have hB := PyramidIidMomentReuse.iid_anchor_volume_integral_eq ν
  change (∫ w : Fin (d + 1) → Fin d → ℝ,
    |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw ν (d + 1)) =
    (∫ z : (Fin d → Fin d → ℝ) × (Fin d → ℝ),
      |liftedDeterminant z.1 z.2| ∂(iidLaw ν d).prod ν) at hB
  unfold determinantLawDefect at hD
  simpa only [id_eq, ← hB, sub_nonneg] using hD

variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

theorem finite_halfspace_horizontal_moment_pos (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (∫ w : Fin d → Fin d → ℝ, |horizontalDeterminant w| ∂iidLaw (finiteHalfspaceConeLaw n h) d) := by
  rw [finite_halfspace_horizontal_first_moment n h hn hh hinj hc]
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d)))
  exact mul_pos (div_pos (by exact_mod_cast Nat.factorial_pos d)
    (pow_pos (mul_pos hd (finite_halfspace_volume_pos n h hn hh hc)) _))
    (finite_halfspace_projection_body_volume_pos n h hn hh hc)

theorem finite_halfspace_lifted_moment_pos (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) := by
  let ν := finiteHalfspaceConeLaw n h
  let : IsProbabilityMeasure ν := finite_halfspace_cone_probability n h hn hh hinj hc
  have hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν :=
    fun i => finite_cone_integrable _ _ _ _ _
  exact (finite_halfspace_horizontal_moment_pos n h hn hh hinj hc).trans_le
    (centered_iid_lifted_moment_ge_horizontal ν hX (finite_halfspace_cone_centered n h hn hh hinj hc))

theorem finite_halfspace_entryDefect_moment (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    (d + 1 : ℝ) *
      (∫ w : Fin d → Fin d → ℝ, |horizontalDeterminant w| ∂iidLaw (finiteHalfspaceConeLaw n h) d) *
        entryDefect (finiteHalfspaceSet n h) =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) -
      (∫ w : Fin d → Fin d → ℝ, |horizontalDeterminant w| ∂iidLaw (finiteHalfspaceConeLaw n h) d) := by
  unfold entryDefect
  rw [finite_halfspace_entryA_lifted_moment n h hn hh hinj hc]
  have hA := finite_halfspace_horizontal_moment_pos n h hn hh hinj hc
  have hd : finrank ℝ (Space d) = d := by simp [Space]
  rw [hd]
  field_simp [hA.ne']

theorem finite_halfspace_defect_over_first_moment (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    ((∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) -
      (∫ w : Fin d → Fin d → ℝ, |horizontalDeterminant w| ∂iidLaw (finiteHalfspaceConeLaw n h) d)) /
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) =
      (d + 1 : ℝ) * entryDefect (finiteHalfspaceSet n h) /
        (1 + (d + 1 : ℝ) * entryDefect (finiteHalfspaceSet n h)) := by
  have hD := finite_halfspace_entryDefect_moment n h hn hh hinj hc
  have hA := finite_halfspace_horizontal_moment_pos n h hn hh hinj hc
  have hB := finite_halfspace_lifted_moment_pos n h hn hh hinj hc
  have he : 1 + (d + 1 : ℝ) * entryDefect (finiteHalfspaceSet n h) ≠ 0 := by
    intro hz
    have heq : (∫ w : Fin (d + 1) → Fin d → ℝ,
      |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) = 0 := by
      nlinarith [hD]
    exact hB.ne' heq
  field_simp [hA.ne', hB.ne', he]
  nlinarith [hD]

end Entry005
