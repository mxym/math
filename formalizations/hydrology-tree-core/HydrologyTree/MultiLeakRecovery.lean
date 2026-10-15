import HydrologyTree.MultiLeakModel

/-! Exhaustive reverse reduction of every physical full-target MULTI-leak matrix
to an actual single-root reference and a normalized nonnegative-leak gauge. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The required single-root reference and every state scale are constructed
from actual arbitrary multi-leak matrices, not hypothesized in the fibre. -/
theorem multiLeak_reference_exists {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1)
    (A : MultiLeakMatrixFiber G o r w) :
    ∃ x : PositiveStieltjesFiber p.tree r w,
      ∃ h : NonnegativeLeakGauge (graphCompartmentMatrix G o (graphRateEquiv p x.val)) o,
        A.val=diagonalGauge h.val (graphCompartmentMatrix G o (graphRateEquiv p x.val)) := by
  let M := A.val.submatrix p.vertices p.vertices
  have hM : HasTreeMatrixSupport p.tree M := by
    intro i j hij hn
    exact A.property.1.1 _ _ (fun h => hij (p.vertices.injective h))
      (fun h => hn ((p.adj_iff i j).mpr h))
  have hMP : M.charpoly=stieltjesDenominator r :=
    (charpoly_submatrix_equiv A.val p.vertices).trans A.property.2.1
  have hMF : diagonalCofactor M 0=stieltjesNumerator r w := by
    rw [diagonalCofactor_submatrix_equiv,p.root_eq]
    exact A.property.2.2
  obtain ⟨x,h,hh,ho,hMx⟩ := supported_positive_diagonal_realization p.tree M hM r w hr hpos hw hm hMP hMF
  let H : V → ℝ := fun v => h (p.vertices.symm v)
  let B := graphCompartmentMatrix G o (graphRateEquiv p x.val)
  have hH : ∀ v,H v ≠ 0 := fun v => hh _
  have hHo : H o=1 := by
    dsimp only [H]
    have he := congrArg (fun v : V => h (p.vertices.symm v)) p.root_eq
    simpa only [Equiv.symm_apply_apply,ho] using he.symm
  have hA : A.val=diagonalGauge H B := by
    rw [← graphCompartmentMatrix_transport p x.val] at hMx
    ext i j
    have he := congrArg (fun N : TreeMatrix n => N (p.vertices.symm i) (p.vertices.symm j)) hMx
    simpa only [M,Matrix.submatrix_apply,Equiv.apply_symm_apply,diagonalGauge_apply,H,B] using he
  have hp : ∀ v,0<H v := connected_gauge_positive hG.connected o A.val B H hH hHo
    A.property.1.2.1 (positive_graph_edge_entry o _ ((graphRateEquiv_positive_iff p x.val).mpr x.property.1)) hA
  refine ⟨x,⟨H,hp,hHo,?_⟩,hA⟩
  intro j
  rw [← hA]
  exact A.property.1.2.2 j

end HydrologyTree
