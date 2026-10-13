import HydrologyTree.CatenaryCanonical
import HydrologyTree.CoordinateEnergy

/-! Canonical actual physical-tree coefficient arrays. This merely identifies
standard coefficient coordinates with standard real rate-shaped arrays; it
introduces no parameter-dependent normalization or surrogate model. -/
open Polynomial Module Matrix
noncomputable section
namespace HydrologyTree

/-- Ascending characteristic and cofactor coefficients, as ordinary coordinate arrays. -/
def coefficientArrayEquiv (n : ℕ) : PathCoefficients n ≃ₗ[ℝ] TreeRates n :=
  (degreeLTEquiv ℝ (n+1)).prodCongr (degreeLTEquiv ℝ n)

@[simp] lemma coefficientArrayEquiv_first (n : ℕ) (p : PathCoefficients n) (i : Fin (n+1)) :
    (coefficientArrayEquiv n p).1 i = (p.1 : ℝ[X]).coeff i := rfl

@[simp] lemma coefficientArrayEquiv_second (n : ℕ) (p : PathCoefficients n) (i : Fin n) :
    (coefficientArrayEquiv n p).2 i = (p.2 : ℝ[X]).coeff i := rfl

lemma coefficientArrayEquiv_dot (n : ℕ) (p q : PathCoefficients n) :
    physicalRateDot n (coefficientArrayEquiv n p) (coefficientArrayEquiv n q) =
      pathCoefficientDot n p q := rfl

lemma toMatrix_coefficientArrayEquiv (n : ℕ) :
    LinearMap.toMatrix (catenaryArrayOutputBasis n) (catenaryArrayInputBasis n)
      (coefficientArrayEquiv n).toLinearMap = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, catenaryArrayInputBasis, catenaryArrayOutputBasis,
      coefficientArrayEquiv, Matrix.one_apply, Polynomial.degreeLT.basis_repr, Fin.val_inj]

/-- Actual coefficient map in standard rate-shaped coordinate arrays. -/
def normalizedPhysicalTree {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : TreeRates n :=
  coefficientArrayEquiv n (physicalCoefficientMap t x)

/-- The original coefficient-map Jacobian in standard ascending bases. -/
def treeCanonicalJacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  (LinearMap.toMatrix (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
    (fderiv ℝ (physicalCoefficientMap t) x).toLinearMap).det

lemma normalizedPhysicalTree_jacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : DifferentiableAt ℝ (physicalCoefficientMap t) x) :
    endJacobian (normalizedPhysicalTree t) x = treeCanonicalJacobian t x := by
  have h := (coefficientArrayEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    hx.hasFDerivAt
  calc
    _ = LinearMap.det ((coefficientArrayEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (physicalCoefficientMap t) x)).toLinearMap := endJacobian_of_hasFDerivAt h
    _ = _ := by
      rw [← LinearMap.det_toMatrix (catenaryArrayInputBasis n)]
      change (LinearMap.toMatrix _ _ ((coefficientArrayEquiv n).toLinearMap.comp
        (fderiv ℝ (physicalCoefficientMap t) x).toLinearMap)).det = _
      rw [LinearMap.toMatrix_comp (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
        (catenaryArrayInputBasis n), Matrix.det_mul, toMatrix_coefficientArrayEquiv,
        Matrix.det_one, one_mul]
      rfl

end HydrologyTree
