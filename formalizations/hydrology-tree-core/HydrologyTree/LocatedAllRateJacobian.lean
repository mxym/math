import HydrologyTree.LocatedPolynomialWeight
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-! The actual alternate-leak Jacobian polynomial identity, valid at EVERY real
rate vector. Equality on a positive box is converted into equality of formal
multivariate polynomials; singular and zero boundaries are not discarded. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The independently defined formal partial-derivative determinant equals the
actual factor polynomial in the multivariate ring itself, not just generically. -/
theorem formalLocatedJacobian_factorization {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) :
    formalLocatedJacobian p ell=symbolicLocatedWeight p ell := by
  apply MvPolynomial.funext_set (fun _ : GraphCoordinate G => Set.Ioi (0 : ℝ))
    (fun _ => Set.Ioi_infinite (0 : ℝ))
  intro z hz
  let y := (graphRateArrayEquiv G).symm z
  have hy : PositiveGraphRates y :=
    ⟨hz (.inl ()) (Set.mem_univ _),fun d => hz (.inr d) (Set.mem_univ _)⟩
  have h := (formalLocatedJacobian_evaluate p ell y).trans
    ((positive_located_jacobian_matrix_formula hG p ell y hy).trans
      (symbolicLocatedWeight_evaluate p ell y).symm)
  simpa only [y,LinearEquiv.apply_symm_apply] using h

/-- Full all-rate formula using actual leak cofactor and observed matrix factors.
The zero leak, zero directed rates and repeated spectra are all included. -/
theorem locatedGraphJacobian_all_real {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) :
    locatedGraphJacobian p ell y=treeProofOrientation p.tree *
      (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 * graphCoreWeight p ell y := by
  rw [← formalLocatedJacobian_evaluate,formalLocatedJacobian_factorization hG p ell,
    symbolicLocatedWeight_evaluate]

/-- Exactly one rate toward the leak per edge, times observed-subtree edge
products and actual squared sibling resultants. Both roots are explicitly
presented and the sign depends only on the observation-coordinate convention. -/
theorem locatedGraphJacobian_all_real_factored {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (y : GraphRates G) :
    locatedGraphJacobian p ell y=treeProofOrientation p.tree * leakInwardProduct q y *
      matrixEdgeWeight p.tree (graphObservedMatrix p ell y) *
      matrixSiblingResidual p.tree (graphObservedMatrix p ell y) := by
  rw [locatedGraphJacobian_all_real hG,leak_root_cofactor_product q,graphCoreWeight,matrixCoreWeight]
  ring

/-- No presentation premise on the independently defined finite graph is needed.
The same exact ±1 sign works for every leak site and every real parameter vector. -/
theorem finite_graph_all_leak_polynomial_jacobian {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1) :
    ∃ p : RootedTreePresentation n G o,
      (treeProofOrientation p.tree=1 ∨ treeProofOrientation p.tree= -1) ∧
      ∀ (ell : V) (y : GraphRates G),
        DifferentiableAt ℝ (normalizedLocatedGraphCoefficients p ell) y ∧
        locatedGraphJacobian p ell y=treeProofOrientation p.tree *
          (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 * graphCoreWeight p ell y := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  exact ⟨p,treeProofOrientation_sign p.tree,fun ell y =>
    ⟨differentiable_located_coefficients_all_rates p ell y,locatedGraphJacobian_all_real hG p ell y⟩⟩

end HydrologyTree
