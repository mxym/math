import HydrologyTree.GraphFormalDifferential
import HydrologyTree.GraphPositiveWeight

/-! An actual multivariate factor polynomial for an independently defined
alternate-leak coefficient Jacobian. Evaluation commutes with all principal
matrix/cofactor/resultant operations, including at zero-rate boundaries. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def symbolicObservedMatrix {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (ell : V) :
    Matrix (Fin (n+1)) (Fin (n+1)) (GraphRatePolynomial G) :=
  (graphMatrixOver G ell (universalGraphRates G)).submatrix p.vertices p.vertices

lemma symbolicObservedMatrix_evaluate {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) :
    (symbolicObservedMatrix p ell).map (MvPolynomial.eval (graphRateArrayEquiv G y)) =
      graphObservedMatrix p ell y := by
  have h := graphMatrixOver_map (MvPolynomial.eval (graphRateArrayEquiv G y)) ell (universalGraphRates G)
  rw [universalGraphRates_eval,graphMatrixOver_real] at h
  exact congrArg (fun A => A.submatrix p.vertices p.vertices) h

/-- The actual leak-site principal cofactor at zero as a multivariate polynomial. -/
def symbolicLeakCofactor (ell : V) : GraphRatePolynomial G :=
  (graphCofactorOver ell ell (universalGraphRates G)).coeff 0

lemma symbolicLeakCofactor_evaluate (ell : V) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (symbolicLeakCofactor (G := G) ell) =
      (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 := by
  have h := graphCofactorOver_map (MvPolynomial.eval (graphRateArrayEquiv G y)) ell ell (universalGraphRates G)
  rw [universalGraphRates_eval,graphCofactorOver_real] at h
  have hc := congrArg (fun Q : ℝ[X] => Q.coeff 0) h
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa only [symbolicLeakCofactor,Polynomial.coeff_map] using hc

/-- Proposed factor polynomial is built solely from original physical matrix
entries and actual principal resultants, not from a supplied Jacobian premise. -/
def symbolicLocatedWeight {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (ell : V) :
    GraphRatePolynomial G :=
  MvPolynomial.C (treeProofOrientation p.tree) * symbolicLeakCofactor ell *
    matrixCoreWeight p.tree (symbolicObservedMatrix p ell)

lemma symbolicLocatedWeight_evaluate {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (symbolicLocatedWeight p ell) =
      treeProofOrientation p.tree * (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 *
        graphCoreWeight p ell y := by
  rw [symbolicLocatedWeight,map_mul,map_mul,MvPolynomial.eval_C,symbolicLeakCofactor_evaluate,
    matrixCoreWeight_map,symbolicObservedMatrix_evaluate]
  rfl

end HydrologyTree
