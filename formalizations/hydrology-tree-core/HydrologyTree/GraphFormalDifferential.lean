import HydrologyTree.GraphPolynomialModel
import HydrologyTree.LinearConjugation

/-! The independently defined formal polynomial determinant equals the actual
alternate-leak Frechet Jacobian at every real rate vector, including zero rates. -/
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma locatedCoefficients_polynomial_conjugate {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (ell : V) :
    normalizedLocatedGraphCoefficients p ell = fun y => (graphRateArrayEquiv G).symm
      (polynomialCoordinateMap (symbolicLocatedCoefficients p ell) (graphRateArrayEquiv G y)) := by
  funext y
  rw [symbolicLocatedCoefficients_evaluate,LinearEquiv.symm_apply_apply]

/-- No positivity, invertibility or nonzero-coordinate condition is needed. -/
theorem differentiable_located_coefficients_all_rates {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (ell : V) :
    Differentiable ℝ (normalizedLocatedGraphCoefficients p ell) := by
  rw [locatedCoefficients_polynomial_conjugate]
  exact differentiable_linear_conjugate (graphRateArrayEquiv G)
    (polynomialCoordinateMap (symbolicLocatedCoefficients p ell))
    (fun z => (hasFDerivAt_polynomialCoordinateMap _ z).differentiableAt)

/-- Independent formal partial derivatives represent the actual graph Jacobian
in the explicitly fixed input/output coordinates, over ALL real parameters. -/
theorem formalLocatedJacobian_evaluate {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (formalLocatedJacobian p ell) =
      locatedGraphJacobian p ell y := by
  rw [formalLocatedJacobian,formalJacobianPolynomial_evaluate,locatedGraphJacobian,
    locatedCoefficients_polynomial_conjugate]
  exact (endJacobian_linear_conjugate (graphRateArrayEquiv G) _ y
    (hasFDerivAt_polynomialCoordinateMap _ _).differentiableAt).symm

end HydrologyTree
