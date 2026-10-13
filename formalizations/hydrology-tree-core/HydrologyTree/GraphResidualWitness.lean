import HydrologyTree.RankedTriangularResidual
import HydrologyTree.LocatedPolynomialWeight

/-! Uniform coordinate-hyperplane witnesses for every leak location. The
triangular order is rooted at the leak, while all principal residuals remain
rooted at the observation vertex. No finite sample or hidden-factor hypothesis. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma graphObserved_zero_outward {n : ℕ} {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (a : VertexValues n) :
    graphObservedMatrix p ell (graphRateEquiv q (a,0)) =
      (compartmentMatrix q.tree (a,0)).submatrix
        (fun i => q.vertices.symm (p.vertices i)) (fun i => q.vertices.symm (p.vertices i)) := by
  ext i j
  have h := congrArg (fun A : TreeMatrix n => A (q.vertices.symm (p.vertices i))
    (q.vertices.symm (p.vertices j))) (graphCompartmentMatrix_transport q (a,0))
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,graphObservedMatrix] using h

lemma graphResidual_zero_outward_ne_zero {n : ℕ} {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell)
    (a : VertexValues n) (ha : Function.Injective a) :
    matrixSiblingResidual p.tree (graphObservedMatrix p ell (graphRateEquiv q (a,0))) ≠ 0 := by
  rw [graphObserved_zero_outward]
  let e : Fin (n+1) ≃ Fin (n+1) := p.vertices.trans q.vertices.symm
  apply matrixSiblingResidual_ranked_ne_zero p.tree _ (fun i => (e i).val)
    (Fin.val_injective.comp e.injective)
  · intro i j hij
    exact zero_outward_upper_triangular q.tree a hij
  · intro i j hij
    apply e.injective
    apply ha
    have hd : -a (e i) = -a (e j) := by
      simpa only [e,Equiv.trans_apply,Matrix.submatrix_apply,compartment_diagonal,rateChart,map_zero,Pi.zero_apply,add_zero] using hij
    exact neg_injective hd

/-- Ring-valued actual residual, without the separate edge-coordinate monomial. -/
def symbolicLocatedResidual {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (ell : V) :
    GraphRatePolynomial G := matrixSiblingResidual p.tree (symbolicObservedMatrix p ell)

lemma symbolicLocatedResidual_evaluate {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (symbolicLocatedResidual p ell) =
      matrixSiblingResidual p.tree (graphObservedMatrix p ell y) := by
  rw [symbolicLocatedResidual,matrixSiblingResidual_map,symbolicObservedMatrix_evaluate]

/-- Every individual original graph coordinate can vanish while all actual
observed-subtree sibling resultants remain nonzero, at every leak site. -/
theorem locatedResidual_hyperplane_witness {n : ℕ} {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (k : GraphCoordinate G) :
    ∃ y : GraphRates G, graphRateArrayEquiv G y k=0 ∧
      matrixSiblingResidual p.tree (graphObservedMatrix p ell y) ≠ 0 := by
  rcases k with u | d
  · cases u
    refine ⟨graphRateEquiv q (separatingInward 0,0),?_,?_⟩
    · simp only [graphRateArray_leak,graphRateEquiv_leak,separatingInward_self]
    · exact graphResidual_zero_outward_ne_zero p q _ (separatingInward_injective 0)
  · obtain ⟨e,rfl⟩ := (treeDartEquiv q).surjective d
    rcases e with e | e
    · refine ⟨graphRateEquiv q (separatingInward e.succ,0),?_,?_⟩
      · simp only [graphRateArray_dart,graphRateEquiv_inward,separatingInward_self]
      · exact graphResidual_zero_outward_ne_zero p q _ (separatingInward_injective e.succ)
    · refine ⟨graphRateEquiv q (separatingInward 0,0),?_,?_⟩
      · simp only [graphRateArray_dart,graphRateEquiv_outward,Pi.zero_apply]
      · exact graphResidual_zero_outward_ne_zero p q _ (separatingInward_injective 0)

/-- No original leak or directed-edge variable divides the actual sibling
residual polynomial. This is polynomial nondivisibility, not pointwise heuristics. -/
theorem symbolicLocatedResidual_no_coordinate_factor {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (k : GraphCoordinate G) :
    ¬MvPolynomial.X k ∣ symbolicLocatedResidual p ell := by
  rintro ⟨Q,hQ⟩
  obtain ⟨y,hy,hR⟩ := locatedResidual_hyperplane_witness p (leakRootPresentation hG p ell) k
  apply hR
  rw [← symbolicLocatedResidual_evaluate,hQ,map_mul,MvPolynomial.eval_X,hy,zero_mul]

end HydrologyTree
