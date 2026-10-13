import HydrologyTree.RealLocatedPositivity
import HydrologyTree.MatrixStieltjesIdentification
import HydrologyTree.LocatedLeakJacobian

/-! Exhaustive unrestricted-real alternate-leak response fibers. Positivity and
actual Jacobian regularity are proved consequences, not membership restrictions. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma presentation_vertex_card {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    Fintype.card V=n+1 := by simpa only [Fintype.card_fin] using (Fintype.card_congr p.vertices).symm

theorem real_located_response_iff_pair {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    HasLocatedStieltjesResponse o ell y r w ↔
      (graphCompartmentMatrix G ell y).charpoly=stieltjesDenominator r ∧
      diagonalCofactor (graphCompartmentMatrix G ell y) o=stieltjesNumerator r w :=
  matrix_stieltjes_response_iff_pair _ o (presentation_vertex_card p) r w hr hpos hw hm

/-- Every real competitor is positive even when the leakage vertex differs
from the fixed input/observation vertex. No sign or stability premise on y. -/
theorem real_located_response_forces_positive {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) (hy : HasLocatedStieltjesResponse o ell y r w) :
    PositiveGraphRates y := by
  obtain ⟨hP,hF⟩ := (real_located_response_iff_pair p ell y r w hr hpos hw hm).mp hy
  exact real_located_pair_forces_positive hG p ell y r w hr hpos hw hm hP hF

abbrev RealLocatedFiber {n : ℕ} (o ell : V) (r w : Fin (n+1) → ℝ) :=
  {y : GraphRates G // HasLocatedStieltjesResponse o ell y r w}

/-- An equivalence preserving each actual rate vector, now without silently
removing signed, zero-rate, or singular real competitors from the counted set. -/
def realLocatedFiberEquivPositive {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    RealLocatedFiber (G := G) o ell r w ≃ PositiveLocatedFiber (G := G) o ell r w where
  toFun y := ⟨⟨y.val,real_located_response_forces_positive hG p ell y.val r w hr hpos hw hm y.property⟩,y.property⟩
  invFun y := ⟨y.val.val,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def realLocatedRecursiveEquiv {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    RealLocatedFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree :=
  (realLocatedFiberEquivPositive hG p ell r w hr hpos hw hm).trans
    (locatedPositiveRecursiveEquiv hG p ell r w hr hpos hw hm)

theorem real_located_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Finite (RealLocatedFiber (G := G) o ell r w) ∧
      Nat.card (RealLocatedFiber (G := G) o ell r w)=
        n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) := by
  obtain ⟨hf,hc⟩ := located_positive_fiber_exact_card hG p ell r w hr hpos hw hm
  letI := hf
  let E := realLocatedFiberEquivPositive hG p ell r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- Actual Frechet-Jacobian regularity is also forced for every real full-target
solution at every leakage site, with no nonsingularity hypothesis. -/
theorem real_located_full_response_positive_regular {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) (hy : HasLocatedStieltjesResponse o ell y r w) :
    PositiveGraphRates y ∧ locatedGraphJacobian p ell y ≠ 0 := by
  have hp := real_located_response_forces_positive hG p ell y r w hr hpos hw hm hy
  exact ⟨hp,positive_located_full_response_regular hG p ell ⟨y,hp⟩ r w hr hpos hw hm hy⟩

abbrev RealUnknownLeakFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  Σ ell : V,RealLocatedFiber (G := G) o ell r w

theorem real_unknown_leak_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Finite (RealUnknownLeakFiber (G := G) o r w) ∧
      Nat.card (RealUnknownLeakFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ)) := by
  have hc (ell : V) := real_located_fiber_exact_card hG p ell r w hr hpos hw hm
  letI : ∀ ell : V,Finite (RealLocatedFiber (G := G) o ell r w) := fun ell => (hc ell).1
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_sigma]
  simp only [fun ell => (hc ell).2,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]

/-- Every independent finite tree and every leak site, with all real parameters
included. The required presentation is constructed from the actual graph. -/
theorem finite_graph_all_real_leak_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    ∃ p : RootedTreePresentation n G o,∀ ell : V,
      Nonempty (RealLocatedFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
      Finite (RealLocatedFiber (G := G) o ell r w) ∧
      Nat.card (RealLocatedFiber (G := G) o ell r w)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) ∧
      ∀ y : RealLocatedFiber (G := G) o ell r w,PositiveGraphRates y.val ∧ locatedGraphJacobian p ell y.val ≠ 0 := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  refine ⟨p,?_⟩
  intro ell
  obtain ⟨hf,hc⟩ := real_located_fiber_exact_card hG p ell r w hr hpos hw hm
  exact ⟨⟨realLocatedRecursiveEquiv hG p ell r w hr hpos hw hm⟩,hf,hc,
    fun y => real_located_full_response_positive_regular hG p ell y.val r w hr hpos hw hm y.property⟩

end HydrologyTree
