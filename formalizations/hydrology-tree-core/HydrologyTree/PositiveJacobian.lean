import HydrologyTree.JacobianRegularity
import HydrologyTree.PositiveAssignment

/-! Actual coefficient-Jacobian / spectral equivalences for positive physical
trees. No controllability, ODE identification or global fiber-count claim is
made without its corresponding theorem. -/
noncomputable section
namespace HydrologyTree

/-- Positive physical edges: regularity of the full actual coefficient Jacobian
is exactly absence of sibling spectral collisions anywhere in the real tree. -/
theorem positive_tree_jacobian_iff_no_collision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    treeCanonicalJacobian t x ≠ 0 ↔ ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z := by
  have hx : NonzeroTreeEdges x := ⟨fun e => ne_of_gt (ha e),fun e => ne_of_gt (hf e)⟩
  rw [treeJacobian_ne_zero_iff_coprime t x hx]
  exact ⟨coprime_branches_no_sibling_collisions t x,
    coprime_branches_of_no_spectral_collision t x ha hf⟩

/-- A positive-rate reference is singular exactly when an actual sibling
spectral collision exists; no unproved observability premise is present. -/
theorem positive_tree_jacobian_zero_iff_collision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    treeCanonicalJacobian t x = 0 ↔ ∃ z : ℝ, SiblingCollisionSomewhere t x z := by
  classical
  have h := positive_tree_jacobian_iff_no_collision t x ha hf
  constructor
  · intro hj
    by_contra hn
    exact (h.mpr (by simpa only [not_exists] using hn)) hj
  · rintro ⟨z,hz⟩
    by_contra hj
    exact (h.mp hj) z hz

/-- Equality is for the original unreduced polynomials of the real physical
matrix; this does not silently replace them with a cancelled transfer fraction. -/
theorem positive_tree_jacobian_iff_no_cancellation {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    treeCanonicalJacobian t x ≠ 0 ↔ NoRealPhysicalCancellation t x := by
  have hx : NonzeroTreeEdges x := ⟨fun e => ne_of_gt (ha e),fun e => ne_of_gt (hf e)⟩
  rw [positive_tree_jacobian_iff_no_collision t x ha hf,
    noCancellation_iff_noSiblingCollision t x hx]

/-- With a positive root leak, full distinct positive-weight Stieltjes modes
are equivalent to nonsingularity of the ACTUAL coefficient Jacobian. -/
theorem positive_tree_jacobian_iff_full_modes {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    treeCanonicalJacobian t x ≠ 0 ↔ FullPositiveModes t x := by
  rw [positive_tree_jacobian_iff_no_collision t x ha hf,
    physical_full_modes_iff_no_sibling_collisions t x hell ha hf]

/-- For each prescribed recursive subtree factor assignment, a regular
nonzero-edge real reference admits at most one real rate realization. This
is not uniqueness from the root response without specifying the assignment. -/
theorem regular_tree_assignment_unique {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : NonzeroTreeEdges x) (hJ : treeCanonicalJacobian t x ≠ 0)
    (hassign : SameSubtreeCharacteristics t x y) : x = y := by
  exact physical_subtree_assignment_unique t x y hx
    ((treeJacobian_ne_zero_iff_coprime t x hx).mp hJ) hassign

end HydrologyTree
