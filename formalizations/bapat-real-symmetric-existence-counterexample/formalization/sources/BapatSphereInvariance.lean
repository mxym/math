import BapatSphereMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped Pointwise

namespace BapatRealExistence

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def unitSphereHomeomorph (e : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (by intro x; simp [mem_sphere, dist_zero_right])

theorem sphere_cone_preimage (e : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (unitSphereHomeomorph e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨t, ht, y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨t, ht, e z, ⟨unitSphereHomeomorph e z, hz, rfl⟩, ?_⟩
    simp
  · rintro ⟨t, ht, y, ⟨z, hz, rfl⟩, hx⟩
    refine ⟨t, ht, e.symm z, ⟨(unitSphereHomeomorph e).symm z, ?_, rfl⟩, ?_⟩
    · simpa using hz
    · apply e.injective
      simpa using hx

theorem map_toSphere (e : E ≃ₗᵢ[ℝ] E) (μ : Measure E)
    (he : MeasurePreserving e μ μ) :
    μ.toSphere.map (unitSphereHomeomorph e) = μ.toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (unitSphereHomeomorph e).continuous.measurable hs,
    μ.toSphere_apply' ((unitSphereHomeomorph e).continuous.measurable hs),
    μ.toSphere_apply' hs, sphere_cone_preimage]
  congr 1
  calc
    μ (e ⁻¹' (Ioo (0 : ℝ) 1 • ((fun z : sphere (0 : E) 1 => (z : E)) '' s))) =
        μ.map e (Ioo (0 : ℝ) 1 • ((fun z : sphere (0 : E) 1 => (z : E)) '' s)) := by
      simpa using (e.toHomeomorph.measurableEmbedding.map_apply μ
        (Ioo (0 : ℝ) 1 • ((fun z : sphere (0 : E) 1 => (z : E)) '' s))).symm
    _ = _ := by rw [he.map_eq]

theorem map_normalizedSphere (e : E ≃ₗᵢ[ℝ] E) (μ : Measure E)
    (he : MeasurePreserving e μ μ) :
    (normalizedSphere μ).map (unitSphereHomeomorph e) = normalizedSphere μ := by
  rw [normalizedSphere, Measure.map_smul, map_toSphere e μ he]
  exact (unitSphereHomeomorph e).continuous.measurable.aemeasurable

end

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Canonical normalized angular volume is invariant under every real linear
isometry, and hence under complex unitary maps after restriction of scalars. -/
theorem measurePreserving_normalizedSphere (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (unitSphereHomeomorph e)
      (normalizedSphere (volume : Measure E)) (normalizedSphere (volume : Measure E)) :=
  ⟨(unitSphereHomeomorph e).continuous.measurable,
    map_normalizedSphere e volume e.measurePreserving⟩

/-- Isometries preserve every Haar measure: changing its normalization does not
change the measure-preserving property. -/
theorem measurePreserving_haar_linearIsometry (e : E ≃ₗᵢ[ℝ] E)
    (μ : Measure E) [IsAddHaarMeasure μ] : MeasurePreserving e μ μ := by
  have h := isAddLeftInvariant_eq_smul μ (volume : Measure E)
  refine ⟨e.continuous.measurable, ?_⟩
  conv_lhs => rw [h]
  rw [Measure.map_smul, e.measurePreserving.map_eq]
  · exact h.symm
  · exact e.continuous.measurable.aemeasurable

theorem measurePreserving_normalizedSphere_haar (e : E ≃ₗᵢ[ℝ] E)
    (μ : Measure E) [IsAddHaarMeasure μ] :
    MeasurePreserving (unitSphereHomeomorph e) (normalizedSphere μ) (normalizedSphere μ) :=
  ⟨(unitSphereHomeomorph e).continuous.measurable,
    map_normalizedSphere e μ (measurePreserving_haar_linearIsometry e μ)⟩

end InnerProduct
end BapatRealExistence
