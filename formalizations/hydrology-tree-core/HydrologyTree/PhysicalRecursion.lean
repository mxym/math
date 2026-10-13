import HydrologyTree.ChildMatrix
import HydrologyTree.PhysicalRootDecomposition
import HydrologyTree.ArrowCharacteristic

/-! End-to-end root recursions for the original physical tree's characteristic
polynomial and root cofactor, in terms of the proved smaller physical child trees. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma root_outward_child {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    compartmentMatrix t x c.val 0 = outwardByVertex x.2 c.val := by
  rw [compartment_offdiag_parent_formula t x c.val 0 c.property.1]
  simp only [ite_eq_right c.property.1, c.property.2, ite_true, zero_add]

lemma physicalRootBlock_eq_arrow {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalRootBlockMatrix t x = arrowMatrix (-(rateChart t x).1 0)
      (physicalBranchMatrix t x) (branchRootVertex t) (fun c => x.1 c.val)
      (fun c => outwardByVertex x.2 c.val) := by
  unfold physicalRootBlockMatrix arrowMatrix
  congr 1
  · ext u ⟨c,v⟩
    cases u
    simp [rootInwardRow, arrowRow, root_inward_child, branchRootVertex, Subtype.ext_iff]
  · ext ⟨c,v⟩ u
    cases u
    simp [rootOutwardColumn, arrowColumn, root_outward_child, branchRootVertex, Subtype.ext_iff]

lemma diagonalCofactor_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℝ) (e : κ ≃ ι) (i : κ) :
    diagonalCofactor (A.submatrix e e) i = diagonalCofactor A (e i) := by
  change diagonalCofactor (A.reindex e.symm e.symm) i = _
  rw [diagonalCofactor, Matrix.charmatrix_reindex, Matrix.adjugate_reindex]
  rfl

lemma diagonalCofactor_zero {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    diagonalCofactor A 0 = (A.submatrix Fin.succ Fin.succ).charpoly := by
  unfold diagonalCofactor
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j; simp [Matrix.charmatrix_apply_eq]
  · simp [Matrix.charmatrix_apply_ne, h]

/-- Actual child characteristic polynomial, in the rate-preserving smaller tree. -/
def childCharacteristic {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) : ℝ[X] :=
  physicalCharacteristic (childTree t c) (childRates t c x)

def childCofactor {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) : ℝ[X] :=
  physicalRootCofactor (childTree t c) (childRates t c x)

/-- Root cofactor of the original matrix equals the product of all actual child denominators. -/
theorem physicalRootCofactor_child_product {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalRootCofactor t x = ∏ c : RootChild t, childCharacteristic t x c := by
  have h := congrArg (fun M => diagonalCofactor M (.inl ())) (physical_root_block_decomposition t x)
  rw [diagonalCofactor_reindex, rootPartitionEquiv_root, diagonalCofactor_zero,
    physicalRootBlock_eq_arrow] at h
  apply h.trans
  apply (cofactor_arrowMatrix (-(rateChart t x).1 0) (physicalBranchMatrix t x)
    (branchRootVertex t) (fun c => x.1 c.val) (fun c => outwardByVertex x.2 c.val)).trans
  apply Finset.prod_congr rfl
  intro c _
  exact physicalBranch_charpoly_eq t c x

/-- The complete actual physical root characteristic recursion. It holds for
every tree size and every real rate vector, not merely off the singular set. -/
theorem physicalCharacteristic_child_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalCharacteristic t x =
      (X + Polynomial.C ((rateChart t x).1 0)) * (∏ c : RootChild t, childCharacteristic t x c) -
      ∑ c : RootChild t, Polynomial.C (x.1 c.val * outwardByVertex x.2 c.val) * childCofactor t x c *
        ∏ j ∈ Finset.univ.erase c, childCharacteristic t x j := by
  have h := congrArg Matrix.charpoly (physical_root_block_decomposition t x)
  have he := Matrix.charpoly_reindex (rootPartitionEquiv t).symm (compartmentMatrix t x)
  have ht := he.symm.trans h
  rw [physicalRootBlock_eq_arrow] at ht
  have hrec := charpoly_arrowMatrix (-(rateChart t x).1 0) (physicalBranchMatrix t x)
    (branchRootVertex t) (fun c => x.1 c.val) (fun c => outwardByVertex x.2 c.val)
  have hh := ht.trans hrec
  simp only [map_neg, sub_neg_eq_add, physicalBranch_charpoly_eq,
    physicalBranch_cofactor_eq, childCharacteristic, childCofactor, physicalCharacteristic] at hh ⊢
  convert hh using 1
  congr 3

end HydrologyTree
