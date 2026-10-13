import HydrologyTree.MatrixGaugeWeight
import HydrologyTree.GraphLeakCofactor
import HydrologyTree.LocatedLeakJacobian

/-! Remove rational leak relocation from the positive Jacobian identity, leaving
only actual principal matrix polynomials. This is the input to a separately
proved multivariate-polynomial continuation, not itself a boundary assertion. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def graphObservedMatrix {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) : TreeMatrix n :=
  (graphCompartmentMatrix G ell y).submatrix p.vertices p.vertices

def graphCoreWeight {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) : ℝ := matrixCoreWeight p.tree (graphObservedMatrix p ell y)

lemma diagonalGauge_submatrix {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix V V ℝ) (h : V → ℝ) (e : I → V) :
    (diagonalGauge h A).submatrix e e=diagonalGauge (h ∘ e) (A.submatrix e e) := by
  ext i j
  simp only [Matrix.submatrix_apply,diagonalGauge_apply,Function.comp_apply]

lemma graphCoreWeight_relocation {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    graphCoreWeight p o (relocateLeakRates hG ell o y)=graphCoreWeight p ell y := by
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o ⟨y,hy⟩
  rw [graphCoreWeight,graphObservedMatrix,relocateLeakRates_eq_positive hG ell o y hy,hM,
    diagonalGauge_submatrix]
  exact matrixCoreWeight_gauge p.tree
    ((graphCompartmentMatrix G ell y).submatrix p.vertices p.vertices)
    (h ∘ p.vertices) (fun i => ne_of_gt (hh (p.vertices i)))

lemma graph_root_jacobian_matrixWeight {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (y : GraphRates G) :
    graphCanonicalJacobian p y=treeProofOrientation p.tree *
      (diagonalCofactor (graphCompartmentMatrix G o y) o).eval 0 * graphCoreWeight p o y := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [graphCanonicalJacobian_transport,LinearEquiv.symm_apply_apply,root_jacobian_matrixWeight]
  change _ = treeProofOrientation p.tree * (graphRootCofactor o (graphRateEquiv p x)).eval 0 * _
  rw [graphRootCofactor_transport,physicalRootCofactor_eval_zero,
    graphCoreWeight,graphObservedMatrix,graphCompartmentMatrix_transport]

/-- Positive-domain formula with NO transformed parameters or denominators.
The multiplier is an actual leak-root cofactor, and every sibling factor is
computed on the original observed principal subtrees. -/
theorem positive_located_jacobian_matrix_formula {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    locatedGraphJacobian p ell y=treeProofOrientation p.tree *
      (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 * graphCoreWeight p ell y := by
  let z := relocateLeakRates hG ell o y
  have hchar : (graphCompartmentMatrix G o z).charpoly=(graphCompartmentMatrix G ell y).charpoly := by
    dsimp only [z]
    rw [relocateLeakRates_eq_positive hG ell o y hy]
    exact (relocatePositiveLeak_response hG ell o ⟨y,hy⟩).1
  have hcore := graphCoreWeight_relocation hG p ell y hy
  have hz0 := graphCharacteristic_eval_zero_leak p z
  have hy0 := graphCharacteristic_eval_zero_leak (leakRootPresentation hG p ell) y
  apply mul_left_cancel₀ (ne_of_gt hy.1)
  calc
    y.1*locatedGraphJacobian p ell y = z.1*graphCanonicalJacobian p z :=
      locatedGraphJacobian_leak_weight hG p ell y hy
    _ = treeProofOrientation p.tree *
        (z.1*(diagonalCofactor (graphCompartmentMatrix G o z) o).eval 0)*graphCoreWeight p ell y := by
      rw [graph_root_jacobian_matrixWeight,hcore]
      ring
    _ = treeProofOrientation p.tree * (graphCompartmentMatrix G o z).charpoly.eval 0 * graphCoreWeight p ell y := by rw [← hz0]
    _ = treeProofOrientation p.tree * (y.1*(diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0) * graphCoreWeight p ell y := by rw [hchar,hy0]
    _ = _ := by ring

end HydrologyTree
