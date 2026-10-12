import ErdosSimilarityGrowingGaps.SequenceGreedyRouting

namespace ErdosSimilarityGrowingGaps

/-!
Finite assembly of local greedy prefixes.  The prefix lengths are allowed to
depend on both the internal vertex and its child; no schedule, annulus, or
activation hypothesis is needed for the membership statements below.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A common finite test family obtained by taking the union of every local
greedy prefix.  The dependent `Fin` domain records each prefix's endpoint,
while `Finset.biUnion` removes duplicate natural indices automatically. -/
noncomputable def globalGreedyTests
    {M d : ℕ} (B : InternalNode M d → Fin (M - 1) → ℕ)
    (samples : ∀ v child, Fin (B v child + 1) → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun v : InternalNode M d =>
    Finset.univ.biUnion (fun child : Fin (M - 1) =>
      (Finset.univ : Finset (Fin (B v child + 1))).image (samples v child)))

@[simp] theorem mem_globalGreedyTests_of_local
    {M d : ℕ}
    (B : InternalNode M d → Fin (M - 1) → ℕ)
    (samples : ∀ v child, Fin (B v child + 1) → ℕ)
    (v : InternalNode M d) (child : Fin (M - 1))
    (i : Fin (B v child + 1)) :
    samples v child i ∈ globalGreedyTests B samples := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨v, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨child, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem mem_globalGreedyTests_of_local_val
    {M d : ℕ}
    (B : InternalNode M d → Fin (M - 1) → ℕ)
    (samples : ∀ v child, Fin (B v child + 1) → ℕ)
    (v : InternalNode M d) (child : Fin (M - 1))
    (j : ℕ) (hj : j ≤ B v child) :
    samples v child ⟨j, by omega⟩ ∈ globalGreedyTests B samples := by
  exact mem_globalGreedyTests_of_local B samples v child ⟨j, by omega⟩

/-- A common prefix specializes the abstract assembly to greedy samples. -/
noncomputable def globalGreedyWindowTests
    {M d : ℕ} (Z : LogScale)
    (a : InternalNode M d → Fin (M - 1) → ℝ)
    (δ : ℝ) (B : InternalNode M d → Fin (M - 1) → ℕ) : Finset ℕ :=
  globalGreedyTests B (fun v child i =>
    greedyWindowSamples Z (a v child) δ (B v child) i)

theorem mem_globalGreedyWindowTests_of_local
    {M d : ℕ} (Z : LogScale)
    (a : InternalNode M d → Fin (M - 1) → ℝ)
    (δ : ℝ) (B : InternalNode M d → Fin (M - 1) → ℕ)
    (v : InternalNode M d) (child : Fin (M - 1))
    (i : Fin (B v child + 1)) :
    greedyWindowSamples Z (a v child) δ (B v child) i ∈
      globalGreedyWindowTests Z a δ B := by
  exact mem_globalGreedyTests_of_local B
    (fun v child i => greedyWindowSamples Z (a v child) δ (B v child) i)
    v child i

theorem mem_globalGreedyWindowTests_of_local_val
    {M d : ℕ} (Z : LogScale)
    (a : InternalNode M d → Fin (M - 1) → ℝ)
    (δ : ℝ) (B : InternalNode M d → Fin (M - 1) → ℕ)
    (v : InternalNode M d) (child : Fin (M - 1))
    (j : ℕ) (hj : j ≤ B v child) :
    greedyWindowSamples Z (a v child) δ (B v child) ⟨j, by omega⟩ ∈
      globalGreedyWindowTests Z a δ B := by
  exact mem_globalGreedyTests_of_local_val B
    (fun v child i => greedyWindowSamples Z (a v child) δ (B v child) i)
    v child j hj

/-- The global family has at most the sum of the local prefix lengths.  This
bound is deliberately stated before any activation filtering, so it can be
used as the finite cost in a later routing budget. -/
theorem globalGreedyTests_card_le
    {M d : ℕ}
    (B : InternalNode M d → Fin (M - 1) → ℕ)
    (samples : ∀ v child, Fin (B v child + 1) → ℕ) :
    (globalGreedyTests B samples).card ≤
      ∑ v : InternalNode M d, ∑ child : Fin (M - 1), (B v child + 1) := by
  classical
  have hinner (v : InternalNode M d) :
      (Finset.univ.biUnion (fun child : Fin (M - 1) =>
        (Finset.univ : Finset (Fin (B v child + 1))).image (samples v child))).card ≤
        ∑ child : Fin (M - 1), (B v child + 1) := by
    calc
      _ ≤ ∑ child ∈ (Finset.univ : Finset (Fin (M - 1))),
          ((Finset.univ : Finset (Fin (B v child + 1))).image (samples v child)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ child ∈ (Finset.univ : Finset (Fin (M - 1))), (B v child + 1) := by
        refine Finset.sum_le_sum
          (f := fun child : Fin (M - 1) =>
            ((Finset.univ : Finset (Fin (B v child + 1))).image (samples v child)).card)
          (g := fun child : Fin (M - 1) => B v child + 1)
          (s := (Finset.univ : Finset (Fin (M - 1)))) ?_
        intro child hchild
        exact (Finset.card_image_le.trans_eq (by
          simp only [Finset.card_univ, Fintype.card_fin]))
  calc
    (globalGreedyTests B samples).card ≤
        ∑ v ∈ (Finset.univ : Finset (InternalNode M d)),
          (Finset.univ.biUnion (fun child : Fin (M - 1) =>
            (Finset.univ : Finset (Fin (B v child + 1))).image
              (samples v child))).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ (Finset.univ : Finset (InternalNode M d)),
        ∑ child ∈ (Finset.univ : Finset (Fin (M - 1))), (B v child + 1) := by
      refine Finset.sum_le_sum
        (f := fun v : InternalNode M d =>
          (Finset.univ.biUnion (fun child : Fin (M - 1) =>
            (Finset.univ : Finset (Fin (B v child + 1))).image
              (samples v child))).card)
        (g := fun v : InternalNode M d =>
          ∑ child : Fin (M - 1), (B v child + 1))
        (s := (Finset.univ : Finset (InternalNode M d))) ?_
      intro v hv
      exact hinner v
    _ = ∑ v : InternalNode M d, ∑ child : Fin (M - 1), (B v child + 1) := by
      simp

end ErdosSimilarityGrowingGaps
