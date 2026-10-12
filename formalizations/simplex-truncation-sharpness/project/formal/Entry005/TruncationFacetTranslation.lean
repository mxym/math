import Entry005.FiniteHalfspaceConeLaw

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem finite_halfspace_translate_carrier {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ι → E) (h : ι → ℝ) (z : E) :
    finiteHalfspaceSet n (fun i => h i - inner ℝ (n i) z) =
      (fun x => x - z) '' finiteHalfspaceSet n h := by
  ext x
  constructor
  · intro hx
    refine ⟨x + z, ?_, by simp⟩
    intro i
    rw [inner_add_right]
    have hi := hx i
    linarith
  · rintro ⟨y, hy, rfl⟩ i
    rw [inner_sub_right]
    exact sub_le_sub_right (hy i) _

theorem finite_halfspace_translated_facet_chart {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ι → E) (h : ι → ℝ) (z : E) (i : ι) (hn : ‖n i‖ = 1) :
    finiteHalfspaceFacetChart n (fun j => h j - inner ℝ (n j) z) i =
      (fun u : (ℝ ∙ n i)ᗮ => u + (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto z) ⁻¹'
        finiteHalfspaceFacetChart n h i := by
  ext u
  change (∀ j, inner ℝ (n j) ((h i - inner ℝ (n i) z) • n i + (u : E)) ≤
    h j - inner ℝ (n j) z) ↔
    ∀ j, inner ℝ (n j) (h i • n i +
      ((u + (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto z : (ℝ ∙ n i)ᗮ) : E)) ≤ h j
  have he : (h i - inner ℝ (n i) z) • n i + (u : E) + z =
      h i • n i + ((u + (ℝ ∙ n i)ᗮ.orthogonalProjectionOnto z : (ℝ ∙ n i)ᗮ) : E) := by
    have hz := unit_normal_projection_decomposition (n i) z hn
    calc
      _ = (h i - inner ℝ (n i) z) • n i + (u : E) +
          (((ℝ ∙ n i)ᗮ.orthogonalProjectionOnto z : E) + inner ℝ (n i) z • n i) :=
        congrArg (fun y => (h i - inner ℝ (n i) z) • n i + (u : E) + y) hz
      _ = _ := by simp only [Submodule.coe_add]; module
  constructor
  · intro hu j
    rw [← he, inner_add_right]
    linarith [hu j]
  · intro hu j
    have hj := hu j
    rw [← he, inner_add_right] at hj
    linarith

/-- Intrinsic facet areas are unchanged by translating the actual halfspace
body; the chart moves by translation inside the same Euclidean hyperplane. -/
theorem finite_halfspace_facet_area_translation {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ι → E) (h : ι → ℝ) (z : E) (i : ι) (hn : ‖n i‖ = 1) :
    finiteHalfspaceFacetArea n (fun j => h j - inner ℝ (n j) z) i =
      finiteHalfspaceFacetArea n h i := by
  unfold finiteHalfspaceFacetArea
  rw [finite_halfspace_translated_facet_chart n h z i hn, measure_preimage_add_right]

end Entry005
