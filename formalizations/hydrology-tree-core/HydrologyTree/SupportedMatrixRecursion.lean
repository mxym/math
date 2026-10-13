import HydrologyTree.TreeMatrixSupport
import HydrologyTree.CoprimeBranchRecovery

/-! Exact characteristic/cofactor recursion and branch recovery for arbitrary
real tree-supported matrices, without physical sign or column-sum assumptions. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

def matrixChildP {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) : ℝ[X] :=
  (supportedChildMatrix t A c).charpoly

def matrixChildF {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) : ℝ[X] :=
  diagonalCofactor (supportedChildMatrix t A c) 0

def matrixChildNumerator {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) : ℝ[X] :=
  C (A 0 c.val*A c.val 0)*matrixChildF t A c

lemma matrixChildP_monic {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    (matrixChildP t A c).Monic := Matrix.charpoly_monic _

lemma matrixChildP_natDegree {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    (matrixChildP t A c).natDegree=childEdgeCount t c+1 := by simp [matrixChildP]

lemma matrixChildF_monic {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    (matrixChildF t A c).Monic := by
  rw [matrixChildF,diagonalCofactor_zero]
  exact Matrix.charpoly_monic _

lemma matrixChildF_natDegree {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    (matrixChildF t A c).natDegree=childEdgeCount t c := by
  rw [matrixChildF,diagonalCofactor_zero]
  simp

lemma matrixChildNumerator_degree {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    (matrixChildNumerator t A c).degree<(matrixChildP t A c).degree := by
  rw [Polynomial.degree_eq_natDegree (matrixChildP_monic t A c).ne_zero,matrixChildP_natDegree]
  by_cases he : A 0 c.val*A c.val 0=0
  · simp [matrixChildNumerator,he]
  · rw [matrixChildNumerator,Polynomial.degree_C_mul he,
      Polynomial.degree_eq_natDegree (matrixChildF_monic t A c).ne_zero,matrixChildF_natDegree]
    exact_mod_cast Nat.lt_succ_self (childEdgeCount t c)

/-- Actual monic child denominators multiply to the actual root cofactor. -/
theorem supportedMatrix_cofactor_recursion {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) : diagonalCofactor A 0=∏ c, matrixChildP t A c := by
  have h := congrArg (fun M => diagonalCofactor M (.inl ())) (supportedMatrix_arrow t A hA)
  rw [diagonalCofactor_reindex,numberedRootEquiv_zero] at h
  exact h.trans (cofactor_arrowMatrix (A 0 0) (supportedChildMatrix t A)
    (fun _ => 0) (fun c => A 0 c.val) (fun c => A c.val 0))

/-- Actual characteristic recursion, retaining arbitrary original diagonals. -/
theorem supportedMatrix_characteristic_recursion {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) :
    A.charpoly=(X-C (A 0 0))*(∏ c, matrixChildP t A c)-
      branchNumeratorSum (matrixChildP t A) (matrixChildNumerator t A) := by
  have h := congrArg Matrix.charpoly (supportedMatrix_arrow t A hA)
  have he := Matrix.charpoly_reindex (numberedRootEquiv t).symm A
  have hh := he.symm.trans h
  exact hh.trans (charpoly_arrowMatrix (A 0 0) (supportedChildMatrix t A)
    (fun _ => 0) (fun c => A 0 c.val) (fun c => A c.val 0))

lemma supported_branch_numerator_sum {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) :
    branchNumeratorSum (matrixChildP t A) (matrixChildNumerator t A)=
      (X-C (A 0 0))*(∏ c, matrixChildP t A c)-A.charpoly := by
  have h := supportedMatrix_characteristic_recursion t A hA
  linear_combination h

/-- Fixed coprime child factors determine every actual branch numerator of an
arbitrary real matrix. No positive or conservative competitor is assumed. -/
theorem supportedMatrix_numerators_identified {n : ℕ} (t : OrderedTree n) (A B : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (hB : HasTreeMatrixSupport t B)
    (hcop : ∀ c d : RootChild t, c ≠ d → IsCoprime (matrixChildP t A c) (matrixChildP t A d))
    (hchild : ∀ c, matrixChildP t A c=matrixChildP t B c) (hparent : A.charpoly=B.charpoly) :
    matrixChildNumerator t A=matrixChildNumerator t B := by
  have hp := funext hchild
  apply coprime_branch_numerators_unique_mod_product (matrixChildP t A)
    (matrixChildNumerator t A) (matrixChildNumerator t B) hcop (matrixChildNumerator_degree t A)
  · intro c
    rw [hchild c]
    exact matrixChildNumerator_degree t B c
  · refine ⟨C (B 0 0-A 0 0),?_⟩
    rw [supported_branch_numerator_sum t A hA,hp,supported_branch_numerator_sum t B hB,hparent,map_sub]
    ring

/-- Once the child polynomials and their unique numerators agree, the true
root diagonal is determined as well; no assumed trace identity is needed. -/
theorem supportedMatrix_root_diagonal_identified {n : ℕ} (t : OrderedTree n) (A B : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (hB : HasTreeMatrixSupport t B)
    (hcop : ∀ c d : RootChild t, c ≠ d → IsCoprime (matrixChildP t A c) (matrixChildP t A d))
    (hchild : ∀ c, matrixChildP t A c=matrixChildP t B c) (hparent : A.charpoly=B.charpoly) : A 0 0=B 0 0 := by
  have hn := supportedMatrix_numerators_identified t A B hA hB hcop hchild hparent
  have hp := funext hchild
  have he := congrArg (branchNumeratorSum (matrixChildP t B)) hn
  rw [← hp,supported_branch_numerator_sum t A hA] at he
  rw [hp,supported_branch_numerator_sum t B hB,hparent] at he
  have hm : C (B 0 0-A 0 0)*(∏ c, matrixChildP t B c)=0 := by
    rw [map_sub]
    linear_combination he
  have hprod : (∏ c, matrixChildP t B c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => (matrixChildP_monic t B c).ne_zero)
  have hc := (mul_eq_zero.mp hm).resolve_right hprod
  exact (sub_eq_zero.mp (Polynomial.C_eq_zero.mp hc)).symm

/-- Nonzero reference edge products fix both the scale and monic cofactor;
reference positivity is sufficient but the competing matrix is unrestricted. -/
theorem supportedMatrix_child_data_identified {n : ℕ} (t : OrderedTree n) (A B : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (hB : HasTreeMatrixSupport t B)
    (hcop : ∀ c d : RootChild t, c ≠ d → IsCoprime (matrixChildP t A c) (matrixChildP t A d))
    (hchild : ∀ c, matrixChildP t A c=matrixChildP t B c) (hparent : A.charpoly=B.charpoly)
    (hc : ∀ c : RootChild t, A 0 c.val*A c.val 0 ≠ 0) :
    ∀ c : RootChild t, matrixChildF t A c=matrixChildF t B c ∧ A 0 c.val*A c.val 0=B 0 c.val*B c.val 0 := by
  have hn := supportedMatrix_numerators_identified t A B hA hB hcop hchild hparent
  intro c
  have he := congrFun hn c
  have h := scalar_monic_polynomial_unique _ _ (matrixChildF_monic t A c) (matrixChildF_monic t B c)
    _ _ (hc c) he
  exact ⟨h.2,h.1⟩

lemma matrixChildP_physical {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    matrixChildP t (compartmentMatrix t x) c=childCharacteristic t x c := by
  rw [matrixChildP,supportedChild_physical]
  rfl

lemma matrixChildF_physical {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    matrixChildF t (compartmentMatrix t x) c=childCofactor t x c := by
  rw [matrixChildF,supportedChild_physical,diagonalCofactor_zero]
  rfl

end HydrologyTree
