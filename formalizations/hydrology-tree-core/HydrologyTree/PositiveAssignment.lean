import HydrologyTree.SubtreeAssignment
import HydrologyTree.PositiveChildModels
import HydrologyTree.PhysicalModes

/-! Global uniqueness per prescribed subtree-denominator assignment for actual
positive-rate trees without spectral cancellations. Assignment existence and
complete assignment/fiber enumeration are NOT supplied as hypotheses or claimed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Positivity and the actual no-collision criterion prove the recursively
coprime denominators needed by exact constructive branch recovery. -/
theorem coprime_branches_of_no_spectral_collision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (hno : ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z) : CoprimeAtEveryBranch t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [CoprimeAtEveryBranch]
    constructor
    · intro c d hcd
      apply positive_child_characteristics_coprime t x ha hf c d
      intro z hc hd
      apply hno z
      rw [SiblingCollisionSomewhere]
      left
      refine ⟨c,d,hcd,?_,?_⟩
      · simpa [Polynomial.aeval_def] using hc
      · simpa [Polynomial.aeval_def] using hd
    · intro c
      have hc := positive_child_rates t x c ha hf
      apply ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c)
        (childRates t c x) hc.2.1 hc.2.2
      intro z hz
      apply hno z
      rw [SiblingCollisionSomewhere]
      exact Or.inr ⟨c,hz⟩

/-- At most one real realization corresponds to a prescribed recursive
characteristic-factor assignment of a positive noncancelling reference tree.
All child-rate recoveries and the final original-rate permutation are proved. -/
theorem positive_subtree_assignment_unique {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (hno : ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z)
    (hassign : SameSubtreeCharacteristics t x y) : x = y := by
  exact physical_subtree_assignment_unique t x y
    ⟨fun e => ne_of_gt (ha e), fun e => ne_of_gt (hf e)⟩
    (coprime_branches_of_no_spectral_collision t x ha hf hno) hassign

/-- The complete positive-mode hypothesis can be used instead of a no-collision
hypothesis; the actual equivalence was proved from physical energy and spectra. -/
theorem full_modes_subtree_assignment_unique {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (hm : FullPositiveModes t x) (hassign : SameSubtreeCharacteristics t x y) : x = y := by
  exact positive_subtree_assignment_unique t x y ha hf
    ((physical_full_modes_iff_no_sibling_collisions t x hell ha hf).mp hm) hassign

end HydrologyTree
