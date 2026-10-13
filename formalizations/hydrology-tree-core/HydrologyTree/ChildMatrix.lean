import HydrologyTree.BranchConservation
import HydrologyTree.Resolvent
import HydrologyTree.EdgeCharacteristic

/-! Complete identification of a renumbered physical principal branch with
its smaller conservative child tree. No diagonal or conservation bridge is assumed. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Column sums and off-diagonal entries uniquely determine a finite matrix. -/
lemma matrix_eq_of_offdiag_of_column_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hoff : ∀ i j, i ≠ j → A i j = B i j)
    (hsum : ∀ j, ∑ i, A i j = ∑ i, B i j) : A = B := by
  ext i j
  by_cases h : i = j
  · subst i
    have ha := Finset.sum_erase_add Finset.univ (fun i => A i j) (Finset.mem_univ j)
    have hb := Finset.sum_erase_add Finset.univ (fun i => B i j) (Finset.mem_univ j)
    have he : (∑ i ∈ Finset.univ.erase j, A i j) = ∑ i ∈ Finset.univ.erase j, B i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hoff i j (Finset.ne_of_mem_erase hi)
    have htot := hsum j
    linarith
  · exact hoff i j h

/-- The actual principal branch is exactly the conservative smaller child model.
The original exit-to-parent rate is retained as its single root leak. -/
theorem physicalBranch_eq_childTree {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    (physicalBranchMatrix t x c).submatrix (childEnumeration t c) (childEnumeration t c) =
      compartmentMatrix (childTree t c) (childRates t c x) := by
  apply matrix_eq_of_offdiag_of_column_sum
  · intro i j hij
    exact (childMatrix_offdiag t c x i j hij).symm
  · intro j
    change (∑ i, compartmentMatrix t x (childEnumeration t c i).val (childEnumeration t c j).val) = _
    rw [childPrincipal_column_sum, compartment_column_sum, childRates_leak]

/-- Child characteristic polynomials are the actual original principal-block determinants. -/
theorem physicalBranch_charpoly_eq {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    (physicalBranchMatrix t x c).charpoly = physicalCharacteristic (childTree t c) (childRates t c x) := by
  have h := congrArg Matrix.charpoly (physicalBranch_eq_childTree t c x)
  have he := Matrix.charpoly_reindex (childEnumeration t c).toEquiv.symm (physicalBranchMatrix t x c)
  exact he.symm.trans h

/-- The characteristic adjugate transports the actual branch root cofactor. -/
theorem physicalBranch_cofactor_eq {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    diagonalCofactor (physicalBranchMatrix t x c) (branchRootVertex t c) =
      physicalRootCofactor (childTree t c) (childRates t c x) := by
  have h := congrArg (fun A => diagonalCofactor A (0 : Fin (childEdgeCount t c+1)))
    (physicalBranch_eq_childTree t c x)
  have ht : diagonalCofactor ((physicalBranchMatrix t x c).submatrix
      (childEnumeration t c) (childEnumeration t c)) 0 =
      diagonalCofactor (physicalBranchMatrix t x c) (branchRootVertex t c) := by
    change diagonalCofactor ((physicalBranchMatrix t x c).reindex
      (childEnumeration t c).toEquiv.symm (childEnumeration t c).toEquiv.symm) 0 = _
    rw [diagonalCofactor, Matrix.charmatrix_reindex, Matrix.adjugate_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact congrArg (diagonalCofactor (physicalBranchMatrix t x c)) (childEnumeration_zero t c)
  rw [ht] at h
  apply h.trans
  unfold diagonalCofactor physicalRootCofactor
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix_apply_eq]
  · simp [Matrix.charmatrix_apply_ne, hij]

end HydrologyTree
