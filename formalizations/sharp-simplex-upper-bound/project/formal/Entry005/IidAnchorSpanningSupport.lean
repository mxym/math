import Entry005.IidAnchorAffineDeterminant
import Entry005.IidAnchorFirstMomentPositive
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open MeasureTheory

namespace Entry005

theorem exists_affineIndependent_anchor_tuple_of_affineSpan_top {d : ℕ}
    (s : Set (Fin d → ℝ)) (hspan : affineSpan ℝ s = ⊤) :
    ∃ w : Fin (d + 1) → Fin d → ℝ, (∀ i, w i ∈ s) ∧ AffineIndependent ℝ w := by
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis (k := ℝ) hspan
  let := b.finite
  let : Fintype t := Fintype.ofFinite t
  have hc : Fintype.card t = d + 1 := by
    simpa using b.card_eq_finrank_add_one
  let e : t ≃ Fin (d + 1) := Fintype.equivOfCardEq (by simp [hc])
  refine ⟨fun i => b (e.symm i), ?_, ?_⟩
  · intro i
    rw [hb]
    exact hts (e.symm i).property
  · exact b.ind.comp_embedding e.symm.toEmbedding

theorem exists_nonsingular_support_anchor_tuple_of_affineSpan_top {d : ℕ}
    (ν : Measure (Fin d → ℝ)) (hspan : affineSpan ℝ ν.support = ⊤) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support) ∧ (anchorMatrix w).det ≠ 0 := by
  obtain ⟨w, hw, hind⟩ := exists_affineIndependent_anchor_tuple_of_affineSpan_top ν.support hspan
  exact ⟨w, hw, selected_anchor_det_ne_zero_of_raw_affineIndependent w hind⟩

theorem iid_anchor_volume_integral_pos_of_support_affineSpan_top {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hspan : affineSpan ℝ ν.support = ⊤) :
    0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1) := by
  obtain ⟨w, hw, hdet⟩ := exists_nonsingular_support_anchor_tuple_of_affineSpan_top ν hspan
  exact iid_anchor_volume_integral_pos_of_support_det_ne_zero ν hX w hw hdet

theorem iid_anchor_volume_integral_pos_of_euclidean_support_affineSpan_top {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hspan : affineSpan ℝ ((WithLp.toLp 2) '' ν.support) = ⊤) :
    0 < ∫ w : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix w).det| ∂iidLaw ν (d + 1) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toAffineEquiv
  have hspan' : affineSpan ℝ (e '' ν.support) = ⊤ := hspan
  apply iid_anchor_volume_integral_pos_of_support_affineSpan_top ν hX
  have h := congrArg (AffineSubspace.map e.symm.toAffineMap) hspan'
  simpa [AffineSubspace.map_span, Set.image_image,
    AffineMap.map_top_of_surjective e.symm.toAffineMap e.symm.surjective] using h

end Entry005
