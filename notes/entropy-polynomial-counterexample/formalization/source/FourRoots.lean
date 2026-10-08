import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Four roots from five alternating strict signs

These reusable lemmas use only continuity and the displayed signs. The strict
signs exclude the endpoints in each application of the intermediate value theorem.
-/

namespace EntropyCounterexample

/-- A positive-to-negative sign change yields a zero strictly between the endpoints. -/
theorem exists_zero_Ioo_of_pos_neg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : 0 < f a) (hb : f b < 0) :
    ∃ x ∈ Set.Ioo a b, f x = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab.le hf ⟨hb.le, ha.le⟩
  refine ⟨x, ⟨?_, ?_⟩, hfx⟩
  · exact lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
  · exact lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)

/-- A negative-to-positive sign change yields a zero strictly between the endpoints. -/
theorem exists_zero_Ioo_of_neg_pos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b) :
    ∃ x ∈ Set.Ioo a b, f x = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab.le hf ⟨ha.le, hb.le⟩
  refine ⟨x, ⟨?_, ?_⟩, hfx⟩
  · exact lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
  · exact lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)

/-- Five alternating signs give a zero in each of four disjoint open intervals. -/
theorem four_roots_in_open_intervals {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : 0 < f (1 / 5)) (h2 : f (2 / 5) < 0)
    (h3 : 0 < f (3 / 5)) (h4 : f (2 / 3) < 0)
    (h5 : 0 < f (4 / 5)) :
    ∃ x1 x2 x3 x4 : ℝ,
      x1 ∈ Set.Ioo (1 / 5) (2 / 5) ∧
      x2 ∈ Set.Ioo (2 / 5) (3 / 5) ∧
      x3 ∈ Set.Ioo (3 / 5) (2 / 3) ∧
      x4 ∈ Set.Ioo (2 / 3) (4 / 5) ∧
      f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 ∧ f x4 = 0 := by
  obtain ⟨x1, hx1, hz1⟩ := exists_zero_Ioo_of_pos_neg
    (by norm_num : (1 : ℝ) / 5 < 2 / 5) hf.continuousOn h1 h2
  obtain ⟨x2, hx2, hz2⟩ := exists_zero_Ioo_of_neg_pos
    (by norm_num : (2 : ℝ) / 5 < 3 / 5) hf.continuousOn h2 h3
  obtain ⟨x3, hx3, hz3⟩ := exists_zero_Ioo_of_pos_neg
    (by norm_num : (3 : ℝ) / 5 < 2 / 3) hf.continuousOn h3 h4
  obtain ⟨x4, hx4, hz4⟩ := exists_zero_Ioo_of_neg_pos
    (by norm_num : (2 : ℝ) / 3 < 4 / 5) hf.continuousOn h4 h5
  exact ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, hz1, hz2, hz3, hz4⟩

/-- The four zeros are strictly ordered and lie strictly between zero and one. -/
theorem four_ordered_roots {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : 0 < f (1 / 5)) (h2 : f (2 / 5) < 0)
    (h3 : 0 < f (3 / 5)) (h4 : f (2 / 3) < 0)
    (h5 : 0 < f (4 / 5)) :
    ∃ x1 x2 x3 x4 : ℝ,
      0 < x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < 1 ∧
      f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 ∧ f x4 = 0 := by
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, hz1, hz2, hz3, hz4⟩ :=
    four_roots_in_open_intervals hf h1 h2 h3 h4 h5
  refine ⟨x1, x2, x3, x4, ?_, ?_, ?_, ?_, ?_, hz1, hz2, hz3, hz4⟩
  · linarith [hx1.1]
  · exact hx1.2.trans hx2.1
  · exact hx2.2.trans hx3.1
  · exact hx3.2.trans hx4.1
  · linarith [hx4.2]

/-- All four roots belong to `(0,1)`, and all six pairs are distinct. -/
theorem four_distinct_roots {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : 0 < f (1 / 5)) (h2 : f (2 / 5) < 0)
    (h3 : 0 < f (3 / 5)) (h4 : f (2 / 3) < 0)
    (h5 : 0 < f (4 / 5)) :
    ∃ x1 x2 x3 x4 : ℝ,
      x1 ∈ Set.Ioo 0 1 ∧ x2 ∈ Set.Ioo 0 1 ∧
      x3 ∈ Set.Ioo 0 1 ∧ x4 ∈ Set.Ioo 0 1 ∧
      x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧
      x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
      f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 ∧ f x4 = 0 := by
  obtain ⟨x1, x2, x3, x4, hx1, h12, h23, h34, hx4, hz1, hz2, hz3, hz4⟩ :=
    four_ordered_roots hf h1 h2 h3 h4 h5
  refine ⟨x1, x2, x3, x4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hz1, hz2, hz3, hz4⟩
  · exact ⟨hx1, (h12.trans h23).trans (h34.trans hx4)⟩
  · exact ⟨hx1.trans h12, h23.trans (h34.trans hx4)⟩
  · exact ⟨(hx1.trans h12).trans h23, h34.trans hx4⟩
  · exact ⟨((hx1.trans h12).trans h23).trans h34, hx4⟩
  · exact h12.ne
  · exact (h12.trans h23).ne
  · exact ((h12.trans h23).trans h34).ne
  · exact h23.ne
  · exact (h23.trans h34).ne
  · exact h34.ne

/-- No chosen pair of real numbers can contain every zero in `(0,1)`. -/
theorem root_outside_any_pair {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : 0 < f (1 / 5)) (h2 : f (2 / 5) < 0)
    (h3 : 0 < f (3 / 5)) (h4 : f (2 / 3) < 0)
    (h5 : 0 < f (4 / 5)) (u v : ℝ) :
    ∃ x ∈ Set.Ioo 0 1, f x = 0 ∧ x ≠ u ∧ x ≠ v := by
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, h12, h13, h14,
    h23, h24, h34, hz1, hz2, hz3, hz4⟩ :=
    four_distinct_roots hf h1 h2 h3 h4 h5
  by_cases h1u : x1 = u
  · by_cases h2v : x2 = v
    · exact ⟨x3, hx3, hz3, by simpa [← h1u] using h13.symm,
        by simpa [← h2v] using h23.symm⟩
    · exact ⟨x2, hx2, hz2, by simpa [← h1u] using h12.symm, h2v⟩
  · by_cases h1v : x1 = v
    · by_cases h2u : x2 = u
      · exact ⟨x3, hx3, hz3, by simpa [← h2u] using h23.symm,
          by simpa [← h1v] using h13.symm⟩
      · exact ⟨x2, hx2, hz2, h2u, by simpa [← h1v] using h12.symm⟩
    · exact ⟨x1, hx1, hz1, h1u, h1v⟩

/-- In particular, the zero set in `(0,1)` cannot consist of exactly two distinct points. -/
theorem not_exactly_two_roots {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : 0 < f (1 / 5)) (h2 : f (2 / 5) < 0)
    (h3 : 0 < f (3 / 5)) (h4 : f (2 / 3) < 0)
    (h5 : 0 < f (4 / 5)) :
    ¬ ∃ u v : ℝ, u ≠ v ∧
      (∀ x : ℝ, x ∈ Set.Ioo 0 1 → (f x = 0 ↔ x = u ∨ x = v)) := by
  rintro ⟨u, v, _, hall⟩
  obtain ⟨x, hx, hzero, hxu, hxv⟩ := root_outside_any_pair hf h1 h2 h3 h4 h5 u v
  exact ((hall x hx).mp hzero).elim hxu hxv

end EntropyCounterexample
