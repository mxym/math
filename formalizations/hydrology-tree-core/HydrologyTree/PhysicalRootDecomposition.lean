import HydrologyTree.BranchMatrixSupport

/-! Exact root/branch block decomposition of the original physical matrix,
constructed from its parent map without a block-structure assumption. -/
open Matrix
noncomputable section
namespace HydrologyTree

abbrev BranchNodesOf {n : ℕ} (t : OrderedTree n) := Σ c : RootChild t, BranchVertex t c

def rootInwardRow {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix Unit (BranchNodesOf t) ℝ :=
  Matrix.of fun _ v => if v.2.val = v.1.val then compartmentMatrix t x 0 v.1.val else 0

def rootOutwardColumn {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (BranchNodesOf t) Unit ℝ :=
  Matrix.of fun v _ => if v.2.val = v.1.val then compartmentMatrix t x v.1.val 0 else 0

/-- The actual physical root block and actual principal child blocks. -/
def physicalRootBlockMatrix {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Matrix (Unit ⊕ BranchNodesOf t) (Unit ⊕ BranchNodesOf t) ℝ :=
  Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => -(rateChart t x).1 0)
    (rootInwardRow t x) (rootOutwardColumn t x)
    (Matrix.blockDiagonal' (fun c : RootChild t => physicalBranchMatrix t x c))

/-- Complete root-child block transport for every original OrderedTree and
all rate vectors, with original boundary-exit diagonals retained. -/
theorem physical_root_block_decomposition {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (compartmentMatrix t x).submatrix (rootPartitionEquiv t) (rootPartitionEquiv t) =
      physicalRootBlockMatrix t x := by
  ext u v
  rcases u with u | ⟨c,u⟩ <;> rcases v with v | ⟨d,v⟩
  · cases u
    cases v
    exact compartment_diagonal t x 0
  · cases u
    exact rootPartition_root_to_branch t x d v
  · cases v
    exact rootPartition_branch_to_root t x c u
  · by_cases h : c = d
    · subst d
      simpa only [physicalRootBlockMatrix, Matrix.fromBlocks_apply₂₂,
        Matrix.blockDiagonal'_apply_eq] using rootPartition_same_block t x c u v
    · simpa only [physicalRootBlockMatrix, Matrix.fromBlocks_apply₂₂,
        Matrix.blockDiagonal'_apply_ne _ u v h] using rootPartition_different_blocks t x c d h u v

end HydrologyTree
