import HydrologyTree.GraphMatrixTransport
import HydrologyTree.PhysicalConstants

/-! Exact determinant-at-zero and leak-root cofactor formulas for all real graph
rates. No division by a rate and no positivity premise occur in the identities. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma presentation_card {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    Fintype.card V=n+1 := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr p.vertices).symm

/-- Every observation presentation yields a separately proved leak-root presentation. -/
def leakRootPresentation {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) : RootedTreePresentation n G ell :=
  Classical.choice (finite_rooted_tree_presentation n G ell hG (presentation_card p))

/-- Product of the actual oriented rates toward the leak, in an explicit
leak-root presentation; this definition is independent of the rate values. -/
def leakInwardProduct {n : ℕ} {ell : V} (q : RootedTreePresentation n G ell)
    (y : GraphRates G) : ℝ := ∏ e : Fin n, y.2 (treeDartEquiv q (.inl e))

lemma leak_root_cofactor_product {n : ℕ} {ell : V} (q : RootedTreePresentation n G ell)
    (y : GraphRates G) :
    (diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0=leakInwardProduct q y := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv q).surjective y
  change (graphRootCofactor ell (graphRateEquiv q x)).eval 0 = _
  rw [graphRootCofactor_transport,physicalRootCofactor_eval_zero]
  simp only [leakInwardProduct,graphRateEquiv_inward]

/-- The actual determinant factors by the sole leak, including lambda=0. -/
theorem graphCharacteristic_eval_zero_leak {n : ℕ} {ell : V}
    (q : RootedTreePresentation n G ell) (y : GraphRates G) :
    (graphCompartmentMatrix G ell y).charpoly.eval 0 =
      y.1*(diagonalCofactor (graphCompartmentMatrix G ell y) ell).eval 0 := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv q).surjective y
  change (graphCharacteristic ell (graphRateEquiv q x)).eval 0 =
    (graphRateEquiv q x).1*(graphRootCofactor ell (graphRateEquiv q x)).eval 0
  rw [graphCharacteristic_transport,graphRootCofactor_transport,graphRateEquiv_leak,
    physicalCharacteristic_eval_zero_leak]

end HydrologyTree
