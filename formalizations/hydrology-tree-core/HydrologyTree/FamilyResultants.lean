import HydrologyTree.FamilyProduct

/-! Exact pairwise resultant expansion of the arbitrary-family product Jacobian. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

/-- One factor for every ordered-by-position pair i<j, repetitions allowed. -/
def pairwiseResultants : List ℝ[X] → ℝ
  | [] => 1
  | p :: ps => (ps.map fun q => p.resultant q).prod * pairwiseResultants ps

lemma familyPolynomials_degree_sum (ms : List ℕ) (x : ProductInput ms) :
    ((familyPolynomials ms x).map Polynomial.natDegree).sum = ms.sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [familyPolynomials, List.map_cons, List.sum_cons, natDegree_monicPoly, ih]

lemma familyPolynomials_monic (ms : List ℕ) (x : ProductInput ms) :
    ∀ p ∈ familyPolynomials ms x, p.Monic := by
  induction ms with
  | nil => simp [familyPolynomials]
  | cons m ms ih =>
    intro p hp
    simp only [familyPolynomials, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact monic_monicPoly _
    · exact ih _ p hp

lemma monic_list_prod (ps : List ℝ[X]) (hs : ∀ p ∈ ps, p.Monic) : ps.prod.Monic := by
  induction ps with
  | nil => exact Polynomial.monic_one
  | cons p ps ih =>
    exact (hs p (by simp)).mul (ih (fun q hq => hs q (by simp [hq])))

lemma natDegree_monic_list_prod (ps : List ℝ[X]) (hs : ∀ p ∈ ps, p.Monic) :
    ps.prod.natDegree = (ps.map Polynomial.natDegree).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := hs p (by simp)
    have ht : ∀ q ∈ ps, q.Monic := fun q hq => hs q (by simp [hq])
    rw [List.prod_cons, Polynomial.natDegree_mul hp.ne_zero (monic_list_prod ps ht).ne_zero,
      ih ht]
    rfl

lemma resultant_list_prod (p : ℝ[X]) (ps : List ℝ[X]) (hs : ∀ q ∈ ps, q.Monic) :
    p.resultant ps.prod = (ps.map fun q => p.resultant q).prod := by
  induction ps with
  | nil => simp
  | cons q qs ih =>
    have hq := hs q (by simp)
    have ht : ∀ r ∈ qs, r.Monic := fun r hr => hs r (by simp [hr])
    rw [List.prod_cons,
      Polynomial.natDegree_mul hq.ne_zero (monic_list_prod qs ht).ne_zero,
      Polynomial.resultant_mul_right _ _ _ _ le_rfl, ih ht]
    rfl

/-- The recursive derivative determinant is exactly the product over all pairs. -/
theorem familyResultant_eq_pairwise (ms : List ℕ) (x : ProductInput ms) :
    familyResultant ms x = pairwiseResultants (familyPolynomials ms x) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change Polynomial.resultant (monicPoly x.1) (monicPoly (familyProduct ms x.2)) m ms.sum *
        familyResultant ms x.2 = _
    rw [ih]
    change _ = ((familyPolynomials ms x.2).map fun q =>
      (monicPoly x.1 : ℝ[X]).resultant q).prod * pairwiseResultants (familyPolynomials ms x.2)
    congr 1
    have h := resultant_list_prod (monicPoly x.1) (familyPolynomials ms x.2)
      (familyPolynomials_monic ms x.2)
    rw [← familyProduct_reconstruct] at h
    simpa only [natDegree_monicPoly] using h

/-- Full all-degree, all-coefficient product-Jacobian formula in pairwise form. -/
theorem familyProductJacobian_eq_pairwise (ms : List ℕ) (x : ProductInput ms) :
    familyProductJacobian ms x = pairwiseResultants (familyPolynomials ms x) := by
  rw [familyProductJacobian_eq, familyResultant_eq_pairwise]

end HydrologyTree
