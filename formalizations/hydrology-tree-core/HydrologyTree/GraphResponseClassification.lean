import HydrologyTree.GraphMatrixTransport
import HydrologyTree.RealFiberClassification

/-! Actual root-response fibers for independently presented finite simple trees.
Both the graph's oriented rates and its matrix inverse entry are independent
definitions. The full bijection is proved through the constructed transport. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def HasGraphStieltjesResponse {n : ℕ} (o : V) (y : GraphRates G) (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ s : ℝ, (graphCharacteristic o y).eval s ≠ 0 → (∀ i, s+r i ≠ 0) →
    graphRootResponse o y s=∑ i, w i/(s+r i)

abbrev GraphResponseFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  {y : GraphRates G // HasGraphStieltjesResponse o y r w}

theorem graph_response_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (r w : Fin (n+1) → ℝ) :
    HasGraphStieltjesResponse o (graphRateEquiv p x) r w ↔ HasStieltjesRootResponse p.tree x r w := by
  simp only [HasGraphStieltjesResponse,HasStieltjesRootResponse,
    graphCharacteristic_transport,graphRootResponse_transport]

/-- Exact actual-rate bijection, without sign or regularity restrictions on either fiber. -/
def graphResponseFiberEquiv {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) : GraphResponseFiber (G := G) o r w ≃ RealResponseFiber p.tree r w where
  toFun y := ⟨(graphRateEquiv p).symm y.val,
    (graph_response_transport p _ r w).mp (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  invFun x := ⟨graphRateEquiv p x.val,(graph_response_transport p x.val r w).mpr x.property⟩
  left_inv y := by apply Subtype.ext; exact (graphRateEquiv p).apply_symm_apply y.val
  right_inv x := by apply Subtype.ext; exact (graphRateEquiv p).symm_apply_apply x.val

/-- Every unrestricted real graph realization of a full positive target has
positive rates on ALL actual graph darts, including the root leak. -/
theorem graph_full_response_positive {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (y : GraphResponseFiber (G := G) o r w) :
    PositiveGraphRates y.val := by
  let x := graphResponseFiberEquiv p r w y
  have hp := (real_full_response_forces_positive_regular p.tree x.val r w hr hpos hw hm x.property).1
  have h := (graphRateEquiv_positive_iff p x.val).mpr hp
  change PositiveGraphRates (graphRateEquiv p ((graphRateEquiv p).symm y.val)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Full recursive allocation classification of the original graph parameter fiber. -/
def graphResponseRecursiveEquiv {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    GraphResponseFiber (G := G) o r w ≃ RecursivePoleAllocations p.tree :=
  (graphResponseFiberEquiv p r w).trans (realResponseRecursiveEquiv p.tree r w hr hpos hw hm)

theorem graph_response_fiber_exact_card {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (GraphResponseFiber (G := G) o r w) ∧
      Nat.card (GraphResponseFiber (G := G) o r w)=
        n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) := by
  obtain ⟨hf,hc⟩ := real_root_response_fiber_exact_card p.tree r w hr hpos hw hm
  letI := hf
  let e := graphResponseFiberEquiv p r w
  exact ⟨Finite.of_injective e e.injective,(Nat.card_congr e).trans hc⟩

/-- No presentation is an input premise: it is constructed from the finite
graph's own tree hypothesis, and the exact count is for its actual graph rates. -/
theorem finite_graph_full_response_classification {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      Nonempty (GraphResponseFiber (G := G) o r w ≃ RecursivePoleAllocations p.tree) ∧
      Finite (GraphResponseFiber (G := G) o r w) ∧
      Nat.card (GraphResponseFiber (G := G) o r w)=n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) ∧
      ∀ y : GraphResponseFiber (G := G) o r w, PositiveGraphRates y.val := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  obtain ⟨hf,hc⟩ := graph_response_fiber_exact_card p r w hr hpos hw hm
  exact ⟨p,⟨graphResponseRecursiveEquiv p r w hr hpos hw hm⟩,hf,hc,
    fun y => graph_full_response_positive p r w hr hpos hw hm y⟩

end HydrologyTree
