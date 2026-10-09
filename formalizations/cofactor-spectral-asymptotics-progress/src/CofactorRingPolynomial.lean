import CofactorRingFamily
import CofactorBinaryPermanent

/-! Dehomogenization of the actual ring product and its subset coefficient expansion. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

def ringPolynomial (d : K → ℕ) (a : K → ℂ) : Polynomial ℂ :=
  ∏ k, (1+Polynomial.C (a k)*Polynomial.X^(2*d k))

theorem ringPolynomial_expand (d : K → ℕ) (a : K → ℂ) :
    ringPolynomial d a = ∑ s : Finset K,
      Polynomial.C (∏ k ∈ s, a k)*Polynomial.X^(2*∑ k ∈ s, d k) := by
  unfold ringPolynomial
  simp_rw [add_comm (1 : Polynomial ℂ)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const_one,mul_one,← map_prod,
    Finset.prod_pow_eq_pow_sum,← Finset.mul_sum]

theorem ringPolynomial_coeff (d : K → ℕ) (a : K → ℂ) (j : ℕ) :
    (ringPolynomial d a).coeff j = ∑ s : Finset K,
      if 2*∑ k ∈ s, d k = j then (∏ k ∈ s, a k) else 0 := by
  rw [ringPolynomial_expand,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [eq_comm] using Polynomial.coeff_C_mul_X_pow
    (∏ k ∈ s, a k) (2*∑ k ∈ s, d k) j

theorem ringFamily_slopePolynomial (r : ℕ) (d : K → ℕ)
    (z : (k : K) → Fin (2*d k) → ℂ) (a : K → ℂ)
    (hz : ∀ k, (∏ j, (MvPolynomial.X (0 : Fin 2)+
      MvPolynomial.C (z k j)*MvPolynomial.X (1 : Fin 2))) =
      MvPolynomial.X (0 : Fin 2)^(2*d k)+
        MvPolynomial.C (a k)*MvPolynomial.X (1 : Fin 2)^(2*d k)) :
    slopePolynomial (ringFamilySlopes r d z) = ringPolynomial d a := by
  let f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![1,Polynomial.X]
  have h := congrArg f (ringFamily_homogeneous_product r d z a hz)
  simpa only [f,map_prod,map_mul,map_add,map_pow,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,one_pow,one_mul,slopePolynomial,ringPolynomial] using h

end
end CofactorSpectral
