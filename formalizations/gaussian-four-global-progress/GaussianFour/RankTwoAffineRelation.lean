import GaussianFour.RankOneBridge
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace MatrixOrder Matrix
namespace GaussianFour
open GaussianMeasureBridge

lemma score_vectorSpan_le_two {d : ℕ} (v : Fin 4 → Space d)
    (hrank : (scoreGram v).rank ≤ 2) :
    Module.finrank ℝ (vectorSpan ℝ (Set.range v)) ≤ 2 := by
  have hs : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2 := by
    rw [← scoreGram_rank_eq_span_rows v]
    exact hrank
  have hsub : vectorSpan ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range v) := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ v 0]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hi : v i ∈ Submodule.span ℝ (Set.range v) :=
      Submodule.subset_span (s := Set.range v) ⟨i, rfl⟩
    have h0 : v (0 : Fin 4) ∈ Submodule.span ℝ (Set.range v) :=
      Submodule.subset_span (s := Set.range v) ⟨(0 : Fin 4), rfl⟩
    exact sub_mem hi h0
  exact (Submodule.finrank_mono hsub).trans hs

lemma exists_nontrivial_affine_relation_of_scoreGram_rank_le_two {d : ℕ}
    (v : Fin 4 → Space d) (hrank : (scoreGram v).rank ≤ 2) :
    ∃ a : Fin 4 → ℝ, (∑ i, a i) = 0 ∧
      (∑ i, a i • v i) = 0 ∧ ∃ i, a i ≠ 0 := by
  have hdim := score_vectorSpan_le_two v hrank
  have hnot : ¬ AffineIndependent ℝ v := by
    intro ha
    have hc := ha.card_le_finrank_succ
    norm_num at hc
    omega
  rw [affineIndependent_iff_of_fintype] at hnot
  push_neg at hnot
  obtain ⟨a, ha, hsum, i, hi⟩ := hnot
  refine ⟨a, ha, ?_, i, hi⟩
  rw [Finset.weightedVSub_eq_linear_combination (Finset.univ) ha] at hsum
  exact hsum

end GaussianFour



