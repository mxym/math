import HydrologyTree.LeakRelocationWalk
import HydrologyTree.GraphResponseClassification

/-! Exact positive physical fibers with observation at o and the sole leak at
an arbitrary vertex ell. The positive domain is explicit; no unrestricted-real
alternate-leak rigidity or nonroot discharge interpretation is silently claimed. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def graphObservedResponse (o ell : V) (y : GraphRates G) (s : ℝ) : ℝ :=
  (Matrix.scalar V s-graphCompartmentMatrix G ell y)⁻¹ o o

def HasLocatedStieltjesResponse {n : ℕ} (o ell : V) (y : GraphRates G) (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ s : ℝ, (graphCompartmentMatrix G ell y).charpoly.eval s ≠ 0 → (∀ i, s+r i ≠ 0) →
    graphObservedResponse o ell y s=∑ i, w i/(s+r i)

abbrev PositiveLocatedFiber {n : ℕ} (o ell : V) (r w : Fin (n+1) → ℝ) :=
  {y : PositiveGraphRateSpace G // HasLocatedStieltjesResponse o ell y.val r w}

lemma located_response_at_root {n : ℕ} (o : V) (y : GraphRates G) (r w : Fin (n+1) → ℝ) :
    HasLocatedStieltjesResponse o o y r w ↔ HasGraphStieltjesResponse o y r w := Iff.rfl

/-- The actual nonpole observation predicate is invariant when the leak moves. -/
theorem located_response_relocate {n : ℕ} (hG : G.IsTree) (o u v : V)
    (y : PositiveGraphRateSpace G) (r w : Fin (n+1) → ℝ) :
    HasLocatedStieltjesResponse o u y.val r w ↔
      HasLocatedStieltjesResponse o v (relocatePositiveLeak hG u v y).val r w := by
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG u v y
  have hn : ∀ i, h i ≠ 0 := fun i => ne_of_gt (hh i)
  simp only [HasLocatedStieltjesResponse,graphObservedResponse,hM,
    diagonalGauge_charpoly h hn,diagonalGauge_resolvent h hn]

/-- Exact fiber equivalence, preserving the fixed observation vertex while
changing the actual leak vertex and adjusting the physical edge rates. -/
def positiveLocatedFiberEquiv {n : ℕ} (hG : G.IsTree) (o u v : V)
    (r w : Fin (n+1) → ℝ) :
    PositiveLocatedFiber (G := G) o u r w ≃ PositiveLocatedFiber (G := G) o v r w where
  toFun y := ⟨relocatePositiveLeak hG u v y.val,(located_response_relocate hG o u v y.val r w).mp y.property⟩
  invFun y := ⟨(relocatePositiveLeak hG u v).symm y.val,
    (located_response_relocate hG o u v ((relocatePositiveLeak hG u v).symm y.val) r w).mpr
      (by simpa only [Equiv.apply_symm_apply] using y.property)⟩
  left_inv y := by apply Subtype.ext; exact (relocatePositiveLeak hG u v).symm_apply_apply y.val
  right_inv y := by apply Subtype.ext; exact (relocatePositiveLeak hG u v).apply_symm_apply y.val

/-- At the observation root, positivity follows from the full response, giving
a bijection with the earlier unrestricted-real graph fiber. -/
def locatedRootFiberEquivReal {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    PositiveLocatedFiber (G := G) o o r w ≃ GraphResponseFiber (G := G) o r w where
  toFun y := ⟨y.val.val,y.property⟩
  invFun y := ⟨⟨y.val,graph_full_response_positive p r w hr hpos hw hm y⟩,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full recursive classification of positive models for any specified leak
vertex, not necessarily the input/observation root. -/
def locatedPositiveRecursiveEquiv {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    PositiveLocatedFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree :=
  (positiveLocatedFiberEquiv hG o ell o r w).trans
    ((locatedRootFiberEquivReal p r w hr hpos hw hm).trans
      (graphResponseRecursiveEquiv p r w hr hpos hw hm))

/-- The exact positive count is independent of the specified leak location. -/
theorem located_positive_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    Finite (PositiveLocatedFiber (G := G) o ell r w) ∧
      Nat.card (PositiveLocatedFiber (G := G) o ell r w)=
        n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) := by
  obtain ⟨hf,hc⟩ := graph_response_fiber_exact_card p r w hr hpos hw hm
  letI := hf
  let E := (positiveLocatedFiberEquiv hG o ell o r w).trans (locatedRootFiberEquivReal p r w hr hpos hw hm)
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- Every independent finite tree and every proposed leak site have exactly
this many positive realizations; the required tree representation is constructed. -/
theorem finite_graph_arbitrary_leak_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V)
    (hN : Fintype.card V=n+1) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    ∃ p : RootedTreePresentation n G o, ∀ ell : V,
      Nonempty (PositiveLocatedFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
      Finite (PositiveLocatedFiber (G := G) o ell r w) ∧
      Nat.card (PositiveLocatedFiber (G := G) o ell r w)=
        n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  exact ⟨p,fun ell => ⟨⟨locatedPositiveRecursiveEquiv hG p ell r w hr hpos hw hm⟩,
    located_positive_fiber_exact_card hG p ell r w hr hpos hw hm⟩⟩

/-- Models including the unknown leak site itself as part of their parameters. -/
abbrev UnknownLeakFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  Σ ell : V, PositiveLocatedFiber (G := G) o ell r w

/-- Unknown leakage location gives exactly |V| times the specified-location
positive count. This is a cardinality of actual physical models with leak sites,
not an informal multiplication of hypothetical candidate allocations. -/
theorem unknown_leak_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    Finite (UnknownLeakFiber (G := G) o r w) ∧
      Nat.card (UnknownLeakFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ)) := by
  have hc (ell : V) := located_positive_fiber_exact_card hG p ell r w hr hpos hw hm
  letI : ∀ ell : V, Finite (PositiveLocatedFiber (G := G) o ell r w) := fun ell => (hc ell).1
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_sigma]
  simp only [fun ell => (hc ell).2,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]

end HydrologyTree
