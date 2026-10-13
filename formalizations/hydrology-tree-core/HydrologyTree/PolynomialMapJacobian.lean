import HydrologyTree.MultivariateDifferential
import HydrologyTree.EndJacobian

/-! Formal polynomial Jacobians agree with actual Frechet Jacobians in ordinary
finite coordinate spaces. Both the derivative and determinant comparison are checked. -/
noncomputable section
namespace HydrologyTree
open Matrix Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def polynomialCoordinateMap (p : ι → MvPolynomial ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => MvPolynomial.eval x (p i)

def polynomialCoordinateDifferential (p : ι → MvPolynomial ι ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => multivariateDifferential (p i) x

lemma hasFDerivAt_polynomialCoordinateMap (p : ι → MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (polynomialCoordinateMap p) (polynomialCoordinateDifferential p x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_multivariate_eval (p i) x

/-- The determinant of the matrix of actual formal partial derivatives. -/
def formalJacobianPolynomial (p : ι → MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  (Matrix.of fun i j => MvPolynomial.pderiv j (p i)).det

lemma polynomialCoordinateDifferential_matrix (p : ι → MvPolynomial ι ℝ) (x : ι → ℝ) :
    LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
      (polynomialCoordinateDifferential p x).toLinearMap =
        Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (p i)) := by
  ext i j
  simp only [LinearMap.toMatrix_apply,polynomialCoordinateDifferential,ContinuousLinearMap.coe_pi,
    LinearMap.pi_apply,Pi.basisFun_apply]
  change multivariateDifferential (p i) x (Pi.single j 1) = _
  exact multivariateDifferential_basis (p i) x j

/-- Actual evaluation of the formal polynomial determinant equals the actual
Frechet derivative determinant at every real coordinate vector. -/
theorem formalJacobianPolynomial_evaluate (p : ι → MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (formalJacobianPolynomial p) = endJacobian (polynomialCoordinateMap p) x := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_polynomialCoordinateMap p x),
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ ι),polynomialCoordinateDifferential_matrix]
  rw [formalJacobianPolynomial,RingHom.map_det]
  rfl

end HydrologyTree
