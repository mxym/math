import HydrologyTree.StieltjesNumerator

/-! Degree and leading coefficient of the actual finite Stieltjes numerator.
The normalizing mass constraint is used explicitly; signs and distinctness of
poles are not needed for these algebraic identities. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma stieltjesTerm_monic {n : ℕ} (r : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∏ j ∈ Finset.univ.erase i, (X+C (r j))).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_add_C (r j))

lemma stieltjesTerm_natDegree {n : ℕ} (r : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∏ j ∈ Finset.univ.erase i, (X+C (r j))).natDegree = n := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_add_C (r j))]
  simp

lemma stieltjesTerm_top_coefficient {n : ℕ} (r : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∏ j ∈ Finset.univ.erase i, (X+C (r j))).coeff n = 1 := by
  have h : (∏ j ∈ Finset.univ.erase i, (X+C (r j))).coeff
      (∏ j ∈ Finset.univ.erase i, (X+C (r j))).natDegree = 1 := by
    rw [Polynomial.coeff_natDegree]
    exact stieltjesTerm_monic r i
  simpa only [stieltjesTerm_natDegree] using h

lemma stieltjesNumerator_natDegree_le {n : ℕ} (r w : Fin (n+1) → ℝ) :
    (stieltjesNumerator r w).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C,zero_add,stieltjesTerm_natDegree])

lemma stieltjesNumerator_top_coefficient {n : ℕ} (r w : Fin (n+1) → ℝ) :
    (stieltjesNumerator r w).coeff n = ∑ i, w i := by
  simp [stieltjesNumerator,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    stieltjesTerm_top_coefficient]

/-- Exact monicity at every normalized weight vector, including n=0. -/
theorem normalized_stieltjesNumerator_monic {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hw : (∑ i, w i)=1) : (stieltjesNumerator r w).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (stieltjesNumerator_natDegree_le r w)
  rw [stieltjesNumerator_top_coefficient,hw]

theorem normalized_stieltjesNumerator_degree {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hw : (∑ i, w i)=1) : (stieltjesNumerator r w).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (stieltjesNumerator_natDegree_le r w)
  rw [stieltjesNumerator_top_coefficient,hw]
  exact one_ne_zero

lemma stieltjesDenominator_natDegree {n : ℕ} (r : Fin (n+1) → ℝ) :
    (stieltjesDenominator r).natDegree = n+1 := by
  rw [stieltjesDenominator,Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_add_C (r i))]
  simp

end HydrologyTree
