import HydrologyTree.RootBranches

/-! Exact sparsity of the physical tree matrix under its proved root-branch
partition. No partition of the matrix is assumed as a proof input. -/
open Matrix
noncomputable section
namespace HydrologyTree

lemma rootBranch_edge_step {n : ℕ} (t : OrderedTree n) (e : Fin n)
    (hp : t.parent e ≠ 0) :
    rootBranchVertex t e.succ = rootBranchVertex t (t.parent e) := by
  exact rootBranchVertex_step t e.succ (Fin.succ_ne_zero e) hp

/-- Distinct nonroot branches have no direct physical transfer in either direction. -/
theorem compartment_cross_branch_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v w : Fin (n+1)) (hv : v ≠ 0) (hw : w ≠ 0)
    (hb : rootBranchVertex t v ≠ rootBranchVertex t w) :
    compartmentMatrix t x v w = 0 := by
  have hvw : v ≠ w := fun h => hb (congrArg (rootBranchVertex t) h)
  rw [compartment_offdiag_formula t x v w hvw]
  apply Finset.sum_eq_zero
  intro e _
  have h1 : ¬(t.parent e = v ∧ e.succ = w) := by
    rintro ⟨h1,h2⟩
    have hp : t.parent e ≠ 0 := by rwa [h1]
    have hh := rootBranch_edge_step t e hp
    rw [h1,h2] at hh
    exact hb hh.symm
  have h2 : ¬(e.succ = v ∧ t.parent e = w) := by
    rintro ⟨h1,h2⟩
    have hp : t.parent e ≠ 0 := by rwa [h2]
    have hh := rootBranch_edge_step t e hp
    rw [h1,h2] at hh
    exact hb hh
  simp [h1,h2]

/-- Actual principal branch block, retaining the outgoing-to-root diagonal. -/
def physicalBranchMatrix {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    Matrix (BranchVertex t c) (BranchVertex t c) ℝ :=
  (compartmentMatrix t x).submatrix Subtype.val Subtype.val

/-- The reindexed physical matrix has the exact actual branch on each diagonal block. -/
theorem rootPartition_same_block {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (c : RootChild t) (v w : BranchVertex t c) :
    ((compartmentMatrix t x).submatrix (rootPartitionEquiv t) (rootPartitionEquiv t))
      (.inr ⟨c,v⟩) (.inr ⟨c,w⟩) = physicalBranchMatrix t x c v w := rfl

/-- Every cross-block entry of the actual reindexed matrix vanishes. -/
theorem rootPartition_different_blocks {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (c d : RootChild t) (hcd : c ≠ d) (v : BranchVertex t c) (w : BranchVertex t d) :
    ((compartmentMatrix t x).submatrix (rootPartitionEquiv t) (rootPartitionEquiv t))
      (.inr ⟨c,v⟩) (.inr ⟨d,w⟩) = 0 := by
  apply compartment_cross_branch_zero t x v.val w.val
    (branchVertex_ne_zero t c v) (branchVertex_ne_zero t d w)
  intro h
  apply hcd
  exact Subtype.ext (v.property.symm.trans (h.trans w.property))

lemma parentVertex_succ {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    parentVertex t e.succ = t.parent e := rfl

/-- A nondirect descendant has no inward transfer to the root. -/
theorem compartment_root_column_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v : Fin (n+1)) (hv : v ≠ 0) (hp : parentVertex t v ≠ 0) :
    compartmentMatrix t x 0 v = 0 := by
  rw [compartment_offdiag_formula t x 0 v (Ne.symm hv)]
  apply Finset.sum_eq_zero
  intro e _
  have h1 : ¬(t.parent e = 0 ∧ e.succ = v) := by
    rintro ⟨h1,h2⟩
    apply hp
    rw [← h2, parentVertex_succ, h1]
  simp [h1, Fin.succ_ne_zero]

/-- A nondirect descendant receives no outward transfer directly from the root. -/
theorem compartment_root_row_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (v : Fin (n+1)) (hv : v ≠ 0) (hp : parentVertex t v ≠ 0) :
    compartmentMatrix t x v 0 = 0 := by
  rw [compartment_offdiag_formula t x v 0 hv]
  apply Finset.sum_eq_zero
  intro e _
  have h2 : ¬(e.succ = v ∧ t.parent e = 0) := by
    rintro ⟨h1,h2⟩
    apply hp
    rw [← h1, parentVertex_succ, h2]
  simp [h2, Fin.succ_ne_zero]

lemma branch_nonroot_parent_ne_zero {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (v : BranchVertex t c) (hvc : v.val ≠ c.val) : parentVertex t v.val ≠ 0 := by
  intro hp
  have h := rootBranchVertex_child t v.val (branchVertex_ne_zero t c v) hp
  rw [v.property] at h
  exact hvc h.symm

/-- The root row meets a branch only at that branch's actual root vertex. -/
theorem rootPartition_root_to_branch {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (c : RootChild t) (v : BranchVertex t c) :
    compartmentMatrix t x 0 v.val =
      if v.val = c.val then compartmentMatrix t x 0 c.val else 0 := by
  by_cases h : v.val = c.val
  · simp [h]
  · rw [if_neg h]
    exact compartment_root_column_zero t x v.val (branchVertex_ne_zero t c v)
      (branch_nonroot_parent_ne_zero t c v h)

/-- The root column meets a branch only at that branch's actual root vertex. -/
theorem rootPartition_branch_to_root {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (c : RootChild t) (v : BranchVertex t c) :
    compartmentMatrix t x v.val 0 =
      if v.val = c.val then compartmentMatrix t x c.val 0 else 0 := by
  by_cases h : v.val = c.val
  · simp [h]
  · rw [if_neg h]
    exact compartment_root_row_zero t x v.val (branchVertex_ne_zero t c v)
      (branch_nonroot_parent_ne_zero t c v h)

end HydrologyTree
