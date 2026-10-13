import HydrologyTree.BranchMatrixSupport
import Mathlib.Data.Finset.Sort

/-! Canonical increasing renumbering of each physical root branch as a smaller
OrderedTree. The numbering and all parent data are independent of rates. -/
noncomputable section
namespace HydrologyTree

lemma rootBranchVertex_le {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) :
    rootBranchVertex t v ≤ v := by
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hv : v = 0
    · subst v; simp
    · by_cases hp : parentVertex t v = 0
      · rw [rootBranchVertex_child t v hv hp]
      · rw [rootBranchVertex_step t v hv hp]
        exact le_trans (ih _ (parentVertex_lt t v hv)) (le_of_lt (parentVertex_lt t v hv))

lemma branchRoot_min {n : ℕ} (t : OrderedTree n) (c : RootChild t) (v : BranchVertex t c) :
    branchRootVertex t c ≤ v := by
  change c.val ≤ v.val
  exact v.property.symm.le.trans (rootBranchVertex_le t v.val)

lemma branch_card_pos {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    0 < Fintype.card (BranchVertex t c) := by
  classical
  letI : Nonempty (BranchVertex t c) := ⟨branchRootVertex t c⟩
  exact Fintype.card_pos

/-- Number of internal edges in the actual child subtree. -/
def childEdgeCount {n : ℕ} (t : OrderedTree n) (c : RootChild t) : ℕ :=
  Fintype.card (BranchVertex t c) - 1

lemma child_card {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    Fintype.card (BranchVertex t c) = childEdgeCount t c + 1 := by
  unfold childEdgeCount
  have := branch_card_pos t c
  omega

/-- Original vertex order induces a canonical increasing enumeration of a child. -/
def childEnumeration {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    Fin (childEdgeCount t c + 1) ≃o BranchVertex t c :=
  Fintype.orderIsoFinOfCardEq _ (child_card t c)

@[simp] theorem childEnumeration_zero {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    childEnumeration t c 0 = branchRootVertex t c := by
  apply le_antisymm
  · obtain ⟨j,hj⟩ := (childEnumeration t c).surjective (branchRootVertex t c)
    rw [← hj]
    exact (childEnumeration t c).monotone (Fin.zero_le j)
  · exact branchRoot_min t c _

lemma childEnumeration_ne_root {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i : Fin (childEdgeCount t c)) : (childEnumeration t c i.succ).val ≠ c.val := by
  intro h
  have he : childEnumeration t c i.succ = childEnumeration t c 0 := by
    rw [childEnumeration_zero]
    exact Subtype.ext h
  exact Fin.succ_ne_zero i ((childEnumeration t c).injective he)

/-- The parent of a nonroot child vertex belongs to the same branch. -/
def childParentVertex {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i : Fin (childEdgeCount t c)) : BranchVertex t c :=
  ⟨parentVertex t (childEnumeration t c i.succ).val, by
    have hv := branchVertex_ne_zero t c (childEnumeration t c i.succ)
    have hp := branch_nonroot_parent_ne_zero t c (childEnumeration t c i.succ)
      (childEnumeration_ne_root t c i)
    exact (rootBranchVertex_step t _ hv hp).symm.trans (childEnumeration t c i.succ).property⟩

/-- The actual parent map in the child's own topological numbering. -/
def childTree {n : ℕ} (t : OrderedTree n) (c : RootChild t) : OrderedTree (childEdgeCount t c) where
  parent i := (childEnumeration t c).symm (childParentVertex t c i)
  parent_le i := by
    have h : (childEnumeration t c).symm (childParentVertex t c i) < i.succ := by
      apply (childEnumeration t c).lt_iff_lt.mp
      rw [OrderIso.apply_symm_apply]
      exact parentVertex_lt t _ (branchVertex_ne_zero t c (childEnumeration t c i.succ))
    exact Nat.le_of_lt_succ h

@[simp] theorem childTree_parent_transport {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i : Fin (childEdgeCount t c)) :
    (childEnumeration t c ((childTree t c).parent i)).val =
      parentVertex t (childEnumeration t c i.succ).val := by
  exact congrArg Subtype.val ((childEnumeration t c).apply_symm_apply (childParentVertex t c i))

/-- Each child has strictly fewer edges than its original tree. -/
theorem childEdgeCount_lt {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    childEdgeCount t c < n := by
  have hi : Function.Injective (fun v : BranchVertex t c =>
      (⟨v.val, branchVertex_ne_zero t c v⟩ : {v : Fin (n+1) // v ≠ 0})) := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : {v : Fin (n+1) // v ≠ 0} => z.val) h)
  have hc := Fintype.card_le_of_injective _ hi
  have hnon : Fintype.card {v : Fin (n+1) // v ≠ 0} = n := by
    simp
  rw [hnon, child_card] at hc
  omega

end HydrologyTree
