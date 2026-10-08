import GaussianSimplexAlgebra

/-! Equality in finite weighted Cauchy forces every positively weighted
length to be identical. Zero diagonal weights cause no false constraint. -/
open scoped BigOperators
namespace GaussianSimplexAlgebra

lemma weighted_variance_identity {ι : Type*} (s : Finset ι) (w ell : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, w i * (ell i-a)^2) =
      (∑ i ∈ s, w i * ell i^2) - 2*a*(∑ i ∈ s, w i * ell i) + a^2*(∑ i ∈ s, w i) := by
  simp_rw [show ∀ u v z : ℝ, u*(v-z)^2 = u*v^2 - 2*z*(u*v) + z^2*u by intros; ring,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem weighted_cauchy_equality_lengths {ι : Type*} (s : Finset ι) (w ell : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (he : (∑ i ∈ s, w i * ell i)^2 =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * ell i^2)) :
    ∀ i ∈ s, 0 < w i → ell i = (∑ j ∈ s, w j * ell j) / (∑ j ∈ s, w j) := by
  let a := (∑ j ∈ s, w j * ell j) / (∑ j ∈ s, w j)
  have ha : a * (∑ j ∈ s, w j) = ∑ j ∈ s, w j * ell j := div_mul_cancel₀ _ hW.ne'
  have hz : (∑ i ∈ s, w i * (ell i-a)^2) = 0 := by
    rw [weighted_variance_identity]
    have hmul : (∑ j ∈ s, w j) *
        ((∑ i ∈ s, w i * ell i^2) - 2*a*(∑ i ∈ s, w i * ell i) + a^2*(∑ i ∈ s, w i)) = 0 := by
      nlinarith [sq_nonneg (a*(∑ j ∈ s, w j) - (∑ j ∈ s, w j * ell j))]
    exact (mul_eq_zero.mp hmul).resolve_left hW.ne'
  intro i hi hwi
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => mul_nonneg (hw j hj) (sq_nonneg (ell j-a)))).mp hz i hi
  have heq : (ell i-a)^2 = 0 := (mul_eq_zero.mp ht).resolve_left hwi.ne'
  exact sub_eq_zero.mp ((sq_eq_zero_iff).mp heq)

end GaussianSimplexAlgebra
