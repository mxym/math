import Entry005.IntegratedWitness
import Mathlib.Data.Finset.Max

/-! A deterministic, measurable maximum-coordinate choice, including ties. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def coordinateMaximizers {n : ℕ} (a : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => ∀ j, a j ≤ a i)

theorem coordinate_maximizers_nonempty {n : ℕ} (a : Fin (n + 1) → ℝ) :
    (coordinateMaximizers a).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  refine ⟨i, ?_⟩
  simp only [coordinateMaximizers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun j => hi j (Finset.mem_univ j)

def largestCoordinate {n : ℕ} (a : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (coordinateMaximizers a).min' (coordinate_maximizers_nonempty a)

theorem largest_coordinate_max {n : ℕ} (a : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    a j ≤ a (largestCoordinate a) := by
  have h := Finset.min'_mem (coordinateMaximizers a) (coordinate_maximizers_nonempty a)
  exact (Finset.mem_filter.1 h).2 j

theorem largest_coordinate_fiber {n : ℕ} (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    largestCoordinate a = i ↔
      (∀ j, a j ≤ a i) ∧ (∀ j, (∀ k, a k ≤ a j) → i ≤ j) := by
  constructor
  · intro h
    refine ⟨fun j => h ▸ largest_coordinate_max a j, ?_⟩
    intro j hj
    rw [← h]
    exact Finset.min'_le _ j (by simp [coordinateMaximizers, hj])
  · rintro ⟨hi, hleast⟩
    apply le_antisymm
    · exact Finset.min'_le _ i (by simp [coordinateMaximizers, hi])
    · exact hleast _ (fun k => largest_coordinate_max a k)

theorem measurable_largest_coordinate {n : ℕ} {α : Type*} [MeasurableSpace α]
    {a : α → Fin (n + 1) → ℝ} (ha : ∀ i, Measurable (fun x => a x i)) :
    Measurable (fun x => largestCoordinate (a x)) := by
  have hmax (i : Fin (n + 1)) : MeasurableSet {x | ∀ j, a x j ≤ a x i} := by
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter
      (fun j => measurableSet_le (ha j) (ha i))
  apply measurable_to_countable'
  intro i
  have hleast : MeasurableSet {x | ∀ j, (∀ k, a x k ≤ a x j) → i ≤ j} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i ≤ j
    · simp only [hij, implies_true, Set.ofPred_true]; exact MeasurableSet.univ
    · simp only [hij, imp_false]
      exact (hmax j).compl
  convert (hmax i).inter hleast using 1
  ext x
  exact largest_coordinate_fiber (a x) i

theorem largest_coordinate_positive {n : ℕ} {a : Fin (n + 1) → ℝ}
    (hsum : ∑ i, a i = 1) : 0 < a (largestCoordinate a) := by
  by_contra h
  have hsum0 : ∑ i, a i ≤ 0 := Finset.sum_nonpos (fun i _ =>
    (largest_coordinate_max a i).trans (le_of_not_gt h))
  linarith

end Entry005
