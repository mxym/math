import Entry005.CenteredAtomCorrection
import Entry005.FiniteHalfspaceConeLaw

noncomputable section
open MeasureTheory Metric Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

/-- Literal actual facet cone masses, indexed by the same supplied atoms. -/
def finiteHalfspaceAssignedConeWeights {ι : Type*} [Fintype ι] {d : ℕ}
    (n : ι → Space d) (heights : ι → ℝ) : ι → ℝ :=
  fun i => finiteHalfspaceFacetArea n heights i * heights i /
    ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n heights)).toReal)

/-- Probability, balance and atom-law equality are derived from actual facets.
The atom-identification premise is explicit; no polar-simplex construction is asserted. -/
theorem finite_halfspace_assigned_cone_weights
    {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]
    (n : ι → Space d) (heights : ι → ℝ) (w : ι → Fin d → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < heights i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n heights))
    (hatom : ∀ i, finiteConePoint (fun i j => n i j) heights i = w i) :
    (∀ i, 0 ≤ finiteHalfspaceAssignedConeWeights n heights i) ∧
      (∑ i, finiteHalfspaceAssignedConeWeights n heights i = 1) ∧
      (∑ i, finiteHalfspaceAssignedConeWeights n heights i • WithLp.toLp 2 (w i) = 0) ∧
      finiteAtomLaw (finiteHalfspaceAssignedConeWeights n heights) w = finiteHalfspaceConeLaw n heights := by
  have hM := finite_halfspace_normalization_pos n heights hn hh hc
  refine ⟨fun i => div_nonneg
    (mul_nonneg (finite_halfspace_facet_area_nonneg n heights i) (hh i).le) hM.le, ?_, ?_, ?_⟩
  · simp only [finiteHalfspaceAssignedConeWeights]
    rw [← Finset.sum_div,
      finite_halfspace_facet_mass n heights hn hh hinj hc, div_self hM.ne']
  · ext j
    have hpoint (i : ι) : finiteHalfspaceAssignedConeWeights n heights i * w i j =
        (finiteHalfspaceFacetArea n heights i * n i j) /
          ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n heights)).toReal) := by
      have hw := congrArg (fun v : Fin d → ℝ => v j) (hatom i)
      change n i j / heights i = w i j at hw
      rw [← hw]
      dsimp only [finiteHalfspaceAssignedConeWeights]
      field_simp [(hh i).ne', hM.ne']
    have hcoord : ∑ i, finiteHalfspaceAssignedConeWeights n heights i * w i j = 0 := by
      simp_rw [hpoint]
      rw [← Finset.sum_div, finite_halfspace_normal_balance_coordinates n heights hn hinj hc j,
        zero_div]
    simpa using hcoord
  · unfold finiteAtomLaw finiteHalfspaceConeLaw finiteConeLaw
    simp_rw [hatom]
    rfl

/-- Actual normalized finite-body brightness comparison, conditional only on
the displayed identification of its actual facet atoms with the supplied witness. -/
theorem finite_halfspace_centered_assignment_brightness
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {d : ℕ} [Nontrivial (Space d)]
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hνball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hνcenter : ∀ j, (∫ x, x j ∂ν) = 0)
    (n : ι → Space d) (heights : ι → ℝ) (w : ι → Fin d → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < heights i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n heights))
    (hatom : ∀ i, finiteConePoint (fun i j => n i j) heights i = w i)
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (ha : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)))
    (r : (Fin d → ℝ) → ι) (hr : Measurable r)
    (b h : ℝ) (hb : 0 < b) (hherror : 0 ≤ h)
    (hcost : (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν) ≤ h)
    (hball : closedBall (0 : Space d) b ⊆
      convexHull ℝ (Set.range (fun i => WithLp.toLp 2 (w i)))) :
    ∀ u : Space d, ‖u‖ = 1 →
      |projectionVolumeSet (finiteHalfspaceSet n heights) u /
        ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n heights)).toReal) -
        negativeIntegral ν (fun x => dotProduct u x)| ≤ (b⁻¹ + 1) * h / 2 := by
  obtain ⟨_, hsum, hmean, hlaw⟩ := finite_halfspace_assigned_cone_weights n heights w hn hh hinj hc hatom
  obtain ⟨_, _, hbright⟩ := raw_zero_barycentric_weights_assignment_brightness ν hνball hνcenter w hw ha
    (finiteHalfspaceAssignedConeWeights n heights) hsum hmean r hr b h hb hherror hcost hball
  intro u hu
  have h := hbright u hu
  rw [hlaw, finite_halfspace_cone_negative_brightness n heights hn hh hinj hc u hu] at h
  exact h

theorem finite_halfspace_unit_atom_normalized_brightness_le_half
    {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]
    (n : ι → Space d) (heights : ι → ℝ) (w : ι → Fin d → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < heights i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n heights))
    (hatom : ∀ i, finiteConePoint (fun i j => n i j) heights i = w i)
    (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1) (u : Space d) (hu : ‖u‖ = 1) :
    projectionVolumeSet (finiteHalfspaceSet n heights) u /
      ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n heights)).toReal) ≤ 1 / 2 := by
  obtain ⟨hp, hsum, hmean, hlaw⟩ := finite_halfspace_assigned_cone_weights n heights w hn hh hinj hc hatom
  have hf : ∀ i, 0 ≤ |inner ℝ u (WithLp.toLp 2 (w i))| ∧
      |inner ℝ u (WithLp.toLp 2 (w i))| ≤ 1 := by
    intro i
    refine ⟨abs_nonneg _, ?_⟩
    simpa only [hu, one_mul] using (abs_real_inner_le_norm u (WithLp.toLp 2 (w i))).trans
      (mul_le_mul_of_nonneg_left (hw i) (norm_nonneg u))
  have hbound := (finite_probability_test_bounds
    (finiteHalfspaceAssignedConeWeights n heights) _ hp hsum hf).2
  have hnegative := finite_centered_negative_eq_half_absolute
    (fun i => WithLp.toLp 2 (w i)) (finiteHalfspaceAssignedConeWeights n heights) hmean u
  have hid : projectionVolumeSet (finiteHalfspaceSet n heights) u /
      ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n heights)).toReal) =
      ∑ i, finiteHalfspaceAssignedConeWeights n heights i * max (-inner ℝ u (WithLp.toLp 2 (w i))) 0 := by
    rw [← finite_halfspace_cone_negative_brightness n heights hn hh hinj hc u hu,
      ← hlaw, finite_atom_negative_integral_eq_weighted _ _ hp]
    simp only [euclidean_inner_raw]
  rw [hid, hnegative]
  exact div_le_div_of_nonneg_right hbound (by norm_num)

end Entry005
