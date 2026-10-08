import Entry005.PyramidEntryDefect

noncomputable section
open MeasureTheory Module
open scoped BigOperators

namespace Entry005

def actualFacetHorizontalTupleSum {ι : Type*} [Fintype ι] {d : ℕ}
    (n : ι → Space d) (h : ι → ℝ) : ℝ :=
  ∑ b : Fin d → ι,
    |horizontalDeterminant (fun j l => finiteHalfspaceFacetArea n h (b j) * n (b j) l)|

def actualFacetLiftedTupleSum {ι : Type*} [Fintype ι] {d : ℕ}
    (n : ι → Space d) (h : ι → ℝ) : ℝ :=
  ∑ b : Fin (d + 1) → ι,
    |(sampledMatrix (fun i j => finiteHalfspaceFacetArea n h i *
      finiteFacetLift h (fun i k => n i k) i j) b).det|

/-- Actual facet determinant ratio: sums are over all ordered tuples, including
zero repeated-index terms. The geometric identity and denominator positivity
are proved from the real finite body and the frozen pyramid/B bridge. -/
theorem finite_halfspace_entryA_actual_facet_tuple_ratio
    {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]
    (n : ι → Space d) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    entryA (finiteHalfspaceSet n h) = actualFacetLiftedTupleSum n h /
      ((d + 1 : ℝ) * ((d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) *
        actualFacetHorizontalTupleSum n h) := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let a := finiteHalfspaceFacetArea n h
  let M : ℝ := (d : ℝ) * (volume (finiteHalfspaceSet n h)).toReal
  have hd : finrank ℝ (Space d) = d := by simp [Space]
  have hM : 0 < M := by
    simpa only [M, hd] using finite_halfspace_normalization_pos n h hn hh hc
  have hmass : ∑ i, a i * h i = M := by
    simpa only [a, M, hd] using finite_halfspace_facet_mass n h hn hh hinj hc
  have hA := finite_cone_horizontal_determinant_expectation a h (fun i j => n i j) M
    (finite_halfspace_facet_area_nonneg n h) hh hM hmass
  have hB := finite_cone_lifted_determinant_expectation a h (fun i j => n i j) M
    (finite_halfspace_facet_area_nonneg n h) hh hM hmass
  have he := finite_halfspace_entryA_lifted_moment n h hn hh hinj hc
  change entryA (finiteHalfspaceSet n h) = _
  simp only [finiteHalfspaceConeLaw, hd] at he
  change entryA (finiteHalfspaceSet n h) =
    (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteConeLaw a h (fun i j => n i j) M) (d + 1)) /
    ((d + 1 : ℝ) * (∫ w : Fin d → Fin d → ℝ,
        |horizontalDeterminant w| ∂iidLaw (finiteConeLaw a h (fun i j => n i j) M) d)) at he
  rw [hA, hB] at he
  change entryA (finiteHalfspaceSet n h) =
    (actualFacetLiftedTupleSum n h / M ^ (d + 1)) /
      ((d + 1 : ℝ) * (actualFacetHorizontalTupleSum n h / M ^ d)) at he
  change entryA (finiteHalfspaceSet n h) =
    actualFacetLiftedTupleSum n h / ((d + 1 : ℝ) * M * actualFacetHorizontalTupleSum n h)
  rw [he, pow_succ]
  field_simp [hM.ne']

end Entry005
