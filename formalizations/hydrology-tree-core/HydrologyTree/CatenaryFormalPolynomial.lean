import HydrologyTree.FormalTreePolynomial
import HydrologyTree.CatenaryOrientation

/-! Endpoint-path specialization as an identity of genuine formal Jacobian
polynomials, with the usual inward/outward physical variable convention. -/
noncomputable section
namespace HydrologyTree

/-- Standard inward and outward exponents for n+1 path compartments. -/
def catenaryRatePolynomial (n : ℕ) : RatePolynomial n :=
  ∏ e : Fin n, (MvPolynomial.X (.inl e.succ))^(n-e.val) *
    (MvPolynomial.X (.inr e))^(n-e.val-1)

lemma catenaryRatePolynomial_evaluate (n : ℕ) (x : TreeRates n) :
    MvPolynomial.eval (rateEvaluation x) (catenaryRatePolynomial n) =
      ∏ e : Fin n, x.1 e.succ^(n-e.val) * x.2 e^(n-e.val-1) := by
  simp only [catenaryRatePolynomial,map_prod,map_mul,map_pow,MvPolynomial.eval_X]
  rfl

/-- The formal determinant obtained from the actual symbolic path matrix has
exactly the stated monomial, up to a fixed sign. Includes every zero-rate boundary. -/
theorem formal_catenary_jacobian_polynomial (n : ℕ) :
    formalTreeJacobian (pathTree n) =
      MvPolynomial.C (catenaryCanonicalFactor n) * catenaryRatePolynomial n := by
  apply MvPolynomial.funext
  intro u
  let x : TreeRates n := (fun v => u (.inl v),fun e => u (.inr e))
  have hu : rateEvaluation x = u := by funext j; cases j <;> rfl
  rw [← hu,formalTreeJacobian_evaluate,map_mul,MvPolynomial.eval_C,catenaryRatePolynomial_evaluate]
  exact catenaryCanonicalJacobian_eq n x

/-- Polynomial form of the complete all-size endpoint-catenary monomial formula.
The sign is fixed before the rate variables are specialized. -/
theorem catenary_standard_formal_polynomial (n : ℕ) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧
      formalTreeJacobian (pathTree n) = MvPolynomial.C ε *
        ∏ e : Fin n, (MvPolynomial.X (.inl e.succ))^(n-e.val) *
          (MvPolynomial.X (.inr e))^(n-e.val-1) :=
  ⟨catenaryCanonicalFactor n,real_sq_one_sign _ (catenaryCanonicalFactor_sq n),
    formal_catenary_jacobian_polynomial n⟩

end HydrologyTree
