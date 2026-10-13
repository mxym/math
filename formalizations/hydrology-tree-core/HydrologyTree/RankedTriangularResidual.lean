import HydrologyTree.MatrixSiblingWeight
import HydrologyTree.JacobianRegularity
import HydrologyTree.ZeroOutward

/-! Triangular witnesses in arbitrary vertex orders. Any principal submatrix
inherits triangularity after a proved order lift. Distinct diagonal entries
therefore exclude every sibling collision in any observation-root presentation. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma ranked_triangular_charpoly {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (rank : I → ℕ) (hr : Function.Injective rank)
    (hA : ∀ i j, rank j < rank i → A i j=0) :
    A.charpoly=∏ i : I,(X+C (-A i i)) := by
  letI : LinearOrder I := LinearOrder.lift' rank hr
  have ht : A.IsUpperTriangular := fun i j hij => hA i j hij
  rw [Matrix.charpoly_of_isUpperTriangular _ ht]
  simp only [map_neg,sub_eq_add_neg]

lemma ranked_principal_charpoly {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℝ) (rank : I → ℕ)
    (hr : Function.Injective rank) (hA : ∀ i j, rank j < rank i → A i j=0)
    (e : J → I) (he : Function.Injective e) :
    (A.submatrix e e).charpoly=∏ j : J,(X+C (-A (e j) (e j))) :=
  ranked_triangular_charpoly _ (rank ∘ e) (hr.comp he) (fun i j hij => hA _ _ hij)

lemma ranked_child_coprime {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (rank : Fin (n+1) → ℕ) (hr : Function.Injective rank)
    (hA : ∀ i j, rank j < rank i → A i j=0)
    (hd : Function.Injective (fun i => A i i))
    (c d : RootChild t) (hcd : c ≠ d) :
    IsCoprime (principalChildOver t A c).charpoly (principalChildOver t A d).charpoly := by
  rw [principalChildOver,principalChildOver,
    ranked_principal_charpoly A rank hr hA _ (childEnumeration_injective t c),
    ranked_principal_charpoly A rank hr hA _ (childEnumeration_injective t d)]
  apply IsCoprime.prod_left
  intro i _
  apply IsCoprime.prod_right
  intro j _
  apply coprime_linear_of_ne
  intro h
  exact child_enumerations_distinct t c d hcd i j (hd (neg_injective h))

lemma ranked_sibling_resultant_ne_zero {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (rank : Fin (n+1) → ℕ) (hr : Function.Injective rank)
    (hA : ∀ i j, rank j < rank i → A i j=0)
    (hd : Function.Injective (fun i => A i i)) :
    pairwiseResultantsOver (principalChildPolynomialList t A) ≠ 0 := by
  rw [pairwiseResultantsOver_real]
  apply (pairwiseResultants_ne_zero_iff _ (principalChildPolynomialList_monic t A)).mpr
  rw [principalChildPolynomialList,List.pairwise_ofFn]
  intro i j hij
  apply ranked_child_coprime t A rank hr hA hd
  exact fun h => (ne_of_lt hij) ((Fintype.equivFin (RootChild t)).symm.injective h)

/-- All principal sibling residuals are nonzero for every rank-triangular
matrix with injective diagonal, regardless of the root used for decomposition. -/
theorem matrixSiblingResidual_ranked_ne_zero {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (rank : Fin (n+1) → ℕ) (hr : Function.Injective rank)
    (hA : ∀ i j, rank j < rank i → A i j=0)
    (hd : Function.Injective (fun i => A i i)) : matrixSiblingResidual t A ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixSiblingResidual]
    apply mul_ne_zero (pow_ne_zero _ (ranked_sibling_resultant_ne_zero t A rank hr hA hd))
    apply Finset.prod_ne_zero_iff.mpr
    intro c _
    let e := fun i => (childEnumeration t c i).val
    exact ih _ (childEdgeCount_lt t c) (childTree t c) (principalChildOver t A c)
      (rank ∘ e) (hr.comp (childEnumeration_injective t c))
      (fun i j h => hA _ _ h) (hd.comp (childEnumeration_injective t c))

end HydrologyTree
