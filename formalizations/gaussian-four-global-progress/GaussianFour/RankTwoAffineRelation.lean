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

/-- A nonzero affine relation has coefficients of both signs. -/
theorem affine_relation_has_pos_neg {a : Fin 4 → ℝ}
    (hsum : (∑ i, a i) = 0) (hnz : ∀ i, a i ≠ 0) :
    (∃ i, 0 < a i) ∧ ∃ j, a j < 0 := by
  have hpos : ∃ i, 0 < a i := by
    by_contra h
    push_neg at h
    have hle : ∀ i, a i ≤ 0 := h
    have hlt : a (0 : Fin 4) < 0 :=
      lt_of_le_of_ne (hle 0) (hnz 0)
    have hs : ∑ i, a i < 0 := by
      apply Finset.sum_neg' (s := Finset.univ)
      · intro i hi
        exact hle i
      · exact ⟨0, Finset.mem_univ _, hlt⟩
    linarith
  have hneg : ∃ j, a j < 0 := by
    by_contra h
    push_neg at h
    have hge : ∀ i, 0 ≤ a i := h
    have hlt : 0 < a (0 : Fin 4) :=
      lt_of_le_of_ne (hge 0) (hnz 0).symm
    have hs : 0 < ∑ i, a i := by
      apply Finset.sum_pos' (s := Finset.univ)
      · intro i hi
        exact hge i
      · exact ⟨0, Finset.mem_univ _, hlt⟩
    linarith
  exact ⟨hpos, hneg⟩

/- A relation supported on three labels would contradict affine independence of
that triple.  This is the precise nondegeneracy input needed before using the
alternating-sign quadrilateral case. -/
lemma affine_relation_all_coeff_ne_zero_of_triple_affineIndependent {d : ℕ}
    (v : Fin 4 → Space d)
    (htrip : ∀ (s : Finset (Fin 4)), s.card = 3 →
      AffineIndependent ℝ (fun x : s => v x))
    {a : Fin 4 → ℝ} (hsum : (∑ i, a i) = 0)
    (hrel : (∑ i, a i • v i) = 0) (hnz : ∃ i, a i ≠ 0) :
    ∀ i, a i ≠ 0 := by
  intro i hi
  apply hnz.elim
  intro j hj
  by_cases hji : j = i
  · have hj' : a i ≠ 0 := by
      simpa [hji] using hj
    exact hj' hi
  · let s : Finset (Fin 4) := Finset.univ.erase i
    have hcard : s.card = 3 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      norm_num
    have hind := htrip s hcard
    have hsum_s : (∑ x ∈ s, a x) = 0 := by
      rw [Finset.sum_erase (s := Finset.univ) (f := a) hi]
      simpa using hsum
    have hrel_s : (∑ x ∈ s, a x • v x) = 0 := by
      rw [Finset.sum_erase (s := Finset.univ) (f := fun x => a x • v x)]
      · simpa using hrel
      · simp [hi]
    have hsum_sub : (∑ x : s, a x) = 0 := by
      rw [← Finset.sum_subtype s (by intro x; simp [s]) (fun x => a x)]
      exact hsum_s
    have hrel_sub : (∑ x : s, a x • v x) = 0 := by
      rw [← Finset.sum_subtype s (by intro x; simp [s]) (fun x => a x • v x)]
      exact hrel_s
    have hall0 := (affineIndependent_iff.mp hind) Finset.univ
      (fun x : s => a x) hsum_sub hrel_sub
    have hall : ∀ x : s, a x = 0 := fun x => hall0 x (Finset.mem_univ _)
    have haj : a j = 0 := by
      simpa using hall ⟨j, by simp [s, hji]⟩
    exact hj haj


/-- An affine relation among four score rows is constant on the whole
score-price diagram. -/
lemma affine_score_relation_constant {d : ℕ} (v : Fin 4 → Space d)
    (p a : Fin 4 → ℝ) (x : Space d)
    (hvec : (∑ i, a i • v i) = 0) :
    (∑ i, a i * (⟪v i, x⟫ - p i)) = -(∑ i, a i * p i) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hi : (∑ i, a i * ⟪v i, x⟫) = ⟪∑ i, a i • v i, x⟫ := by
    calc
      (∑ i, a i * ⟪v i, x⟫) = ∑ i, ⟪a i • v i, x⟫ := by
        simp [real_inner_smul_left]
      _ = ⟪∑ i, a i • v i, x⟫ := (sum_inner Finset.univ (fun i => a i • v i) x).symm
  rw [hi, hvec]
  simp

/-- The alternating sign pattern makes the two diagonal facet patterns
incompatible with one affine score relation. -/
lemma affine_relation_no_two_diagonal_facets {a s : Fin 4 → ℝ} {K : ℝ}
    (ha0 : 0 < a 0) (ha1 : a 1 < 0) (ha2 : 0 < a 2) (ha3 : a 3 < 0)
    (hsum : (∑ i, a i) = 0)
    (hK : (∑ i, a i * s i) = K)
    (h13 : s 0 = s 2 ∧ s 1 < s 0 ∧ s 3 < s 0)
    (h24 : s 1 = s 3 ∧ s 0 < s 1 ∧ s 2 < s 1) :
    False := by
  have hsum' := hsum
  norm_num [Fin.sum_univ_succ] at hsum'
  have hpos : 0 < K := by
    rw [← hK]
    norm_num [Fin.sum_univ_succ]
    nlinarith [mul_pos (neg_pos.mpr ha1) (sub_pos.mpr h13.2.1),
      mul_pos (neg_pos.mpr ha3) (sub_pos.mpr h13.2.2), hsum']
  have hneg : K < 0 := by
    rw [← hK]
    norm_num [Fin.sum_univ_succ]
    nlinarith [mul_pos ha0 (sub_pos.mpr h24.2.1),
      mul_pos ha2 (sub_pos.mpr h24.2.2), hsum']
  linarith

end GaussianFour


