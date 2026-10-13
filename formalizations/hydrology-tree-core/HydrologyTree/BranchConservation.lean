import HydrologyTree.ChildRates

/-! Conservation in actual principal child blocks. The exit to the original
root becomes exactly one child leak; its value is not discarded or recomputed. -/
open Matrix
noncomputable section
namespace HydrologyTree

lemma root_inward_child {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    compartmentMatrix t x 0 c.val = x.1 c.val := by
  rw [compartment_offdiag_parent_formula t x 0 c.val (Ne.symm c.property.1)]
  simp only [ite_eq_right c.property.1, c.property.2, ite_true, add_zero]

lemma root_column_split {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n)
    (w : BranchVertex t c) :
    (∑ v : Fin (n+1), compartmentMatrix t x v w.val) =
      compartmentMatrix t x 0 w.val +
      ∑ v : BranchVertex t c, compartmentMatrix t x v.val w.val := by
  classical
  rw [← (rootPartitionEquiv t).sum_comp (fun v => compartmentMatrix t x v w.val)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [rootPartitionEquiv_root, rootPartitionEquiv_branch, Fintype.sum_unique]
  congr 1
  rw [Finset.sum_eq_single c]
  · intro d _ hdc
    apply Finset.sum_eq_zero
    intro v _
    exact rootPartition_different_blocks t x d c hdc v w
  · simp

/-- Each actual principal child block loses mass only through its own root. -/
theorem physicalBranch_column_sum {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n)
    (w : BranchVertex t c) :
    (∑ v : BranchVertex t c, physicalBranchMatrix t x c v w) =
      if w.val = c.val then -x.1 c.val else 0 := by
  have h := root_column_split t c x w
  rw [compartment_column_sum, ite_eq_right (branchVertex_ne_zero t c w),
    rootPartition_root_to_branch, root_inward_child] at h
  change (∑ v : BranchVertex t c, compartmentMatrix t x v.val w.val) = _
  by_cases hw : w.val = c.val
  · rw [ite_eq_left hw] at h ⊢
    linarith
  · rw [ite_eq_right hw] at h ⊢
    simpa using h.symm

/-- Column conservation after the canonical increasing child renumbering. -/
theorem childPrincipal_column_sum {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n)
    (j : Fin (childEdgeCount t c+1)) :
    (∑ i : Fin (childEdgeCount t c+1),
      compartmentMatrix t x (childEnumeration t c i).val (childEnumeration t c j).val) =
      if j = 0 then -x.1 c.val else 0 := by
  have h := (childEnumeration t c).toEquiv.sum_comp
    (fun v : BranchVertex t c => compartmentMatrix t x v.val (childEnumeration t c j).val)
  apply h.trans
  change (∑ v : BranchVertex t c, physicalBranchMatrix t x c v (childEnumeration t c j)) = _
  rw [physicalBranch_column_sum]
  have he : (childEnumeration t c j).val = c.val ↔ j = 0 := by
    constructor
    · intro h
      apply (childEnumeration t c).injective
      rw [childEnumeration_zero]
      exact Subtype.ext h
    · intro h
      subst j
      simp [branchRootVertex]
  by_cases hj : j = 0
  · rw [ite_eq_left (he.mpr hj), ite_eq_left hj]
  · rw [ite_eq_right (fun h => hj (he.mp h)), ite_eq_right hj]

end HydrologyTree
