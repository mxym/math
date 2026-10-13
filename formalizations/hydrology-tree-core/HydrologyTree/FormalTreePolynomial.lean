import HydrologyTree.SymbolicCoefficients
import HydrologyTree.PolynomialMapJacobian
import HydrologyTree.TreeExactMultiplicities
import HydrologyTree.LinearConjugation

/-! The algebraic Jacobian formed by formally differentiating the ACTUAL
symbolic characteristic/cofactor coefficient map. Its identity with the
Frechet Jacobian and its exact factor multiplicities are fully derived. -/
open Module
noncomputable section
namespace HydrologyTree

/-- Standard algebraic Jacobian determinant of the actual symbolic coefficients.
This definition does NOT use the claimed factorization or any resultant factor. -/
def formalTreeJacobian {n : ℕ} (t : OrderedTree n) : RatePolynomial n :=
  formalJacobianPolynomial (symbolicCoefficientPolynomials t)

lemma polynomialCoordinateMap_physical_conjugate {n : ℕ} (t : OrderedTree n) :
    polynomialCoordinateMap (symbolicCoefficientPolynomials t) =
      fun u => rateArrayEquiv n (normalizedPhysicalTree t ((rateArrayEquiv n).symm u)) := by
  funext u j
  have hu : rateEvaluation ((rateArrayEquiv n).symm u) = u := by
    rw [← rateArrayEquiv_apply,LinearEquiv.apply_symm_apply]
  rw [rateArrayEquiv_apply]
  change MvPolynomial.eval u (symbolicCoefficientPolynomials t j) = _
  simpa only [hu] using symbolicCoefficientPolynomials_evaluate t ((rateArrayEquiv n).symm u) j

lemma differentiable_normalizedPhysicalTree {n : ℕ} (t : OrderedTree n) :
    Differentiable ℝ (normalizedPhysicalTree t) := by
  exact (coefficientArrayEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.differentiable.comp
    (differentiable_physicalCoefficientMap t)

/-- Formal differentiation and the actual analytic coefficient Jacobian agree
at every real rate assignment. No representation identity is a hypothesis. -/
theorem formalTreeJacobian_evaluate {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    MvPolynomial.eval (rateEvaluation x) (formalTreeJacobian t) = treeCanonicalJacobian t x := by
  rw [formalTreeJacobian,formalJacobianPolynomial_evaluate,
    polynomialCoordinateMap_physical_conjugate,← rateArrayEquiv_apply]
  have h := endJacobian_linear_conjugate (rateArrayEquiv n).symm
    (normalizedPhysicalTree t) (rateArrayEquiv n x)
    (differentiable_normalizedPhysicalTree t _)
  change endJacobian (fun u => rateArrayEquiv n
    (normalizedPhysicalTree t ((rateArrayEquiv n).symm u))) (rateArrayEquiv n x) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.trans (normalizedPhysicalTree_jacobian t x (differentiable_physicalCoefficientMap t x))

/-- Full polynomial factorization, now for the determinant defined by formal
partial differentiation of actual symbolic physical coefficients. -/
theorem formalTreeJacobian_factorization {n : ℕ} (t : OrderedTree n) :
    formalTreeJacobian t =
      MvPolynomial.C (treeProofOrientation t) * symbolicRateMonomial t * symbolicSiblingResidual t :=
  symbolicJacobian_unique t (formalTreeJacobian t) (formalTreeJacobian_evaluate t)

/-- Exact powers dividing the standard formal Jacobian determinant. -/
theorem formalTreeJacobian_exact_powers {n : ℕ} (t : OrderedTree n) (j : SymbolicRateIndex n) :
    (MvPolynomial.X j)^(symbolicRateExponent t j) ∣ formalTreeJacobian t ∧
      ¬(MvPolynomial.X j)^(symbolicRateExponent t j+1) ∣ formalTreeJacobian t := by
  rw [formalTreeJacobian_factorization]
  exact treeJacobian_coordinate_exact_power t j

/-- Exact inward-edge multiplicities, with no positivity or genericity restrictions. -/
theorem formalTreeJacobian_inward_multiplicity {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inl e.succ)) (formalTreeJacobian t) = subtreeVertexCount t e.succ := by
  rw [formalTreeJacobian_factorization]
  exact treeJacobian_inward_multiplicity t e

/-- Exact outward-edge multiplicities, including multiplicity zero at every leaf. -/
theorem formalTreeJacobian_outward_multiplicity {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr e)) (formalTreeJacobian t) = subtreeVertexCount t e.succ-1 := by
  rw [formalTreeJacobian_factorization]
  exact treeJacobian_outward_multiplicity t e

end HydrologyTree
