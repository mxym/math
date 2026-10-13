import HydrologyTree.RealLocatedClassification
import HydrologyTree.MatrixTimeIdentification
import HydrologyTree.LocatedLeakDynamics

/-! Entire unrestricted-real arbitrary-leak continuous-input fibers. Actual
exponential probe trajectories close the reverse implication before positivity
is derived, so the universal output predicate cannot be satisfied vacuously. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Both directions for actual classical histories of arbitrary signed real
models at any leak vertex. Positivity is not a premise of the implication. -/
theorem real_located_continuous_iff_response {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    HasLocatedContinuousRootOutput o ell y r w ↔ HasLocatedStieltjesResponse o ell y r w := by
  constructor
  · intro h
    obtain ⟨x,hx,hPx,hFx⟩ := positive_tree_stieltjes_realization_exists p.tree r w hr hpos hw hm
    let y0 := graphRateEquiv p x
    have hR : HasGraphStieltjesResponse o y0 r w :=
      (graph_response_transport p x r w).mpr
        ((stieltjes_root_response_iff_polynomials p.tree r w hr hpos hw hm x).mpr ⟨hPx,hFx⟩)
    have hH := (graph_root_continuous_iff_response p y0 r w hr hpos hw hm).mpr hR
    let A := graphCompartmentMatrix G ell y
    let B := graphCompartmentMatrix G o y0
    have heq := same_matrix_outputs_cross_identity B A o (by
      intro u hu z q hz hq hz0 hq0 s hs
      exact (hH u hu z hz hz0 s hs).trans (h u hu q hq hq0 s hs).symm)
    have hPB : B.charpoly=stieltjesDenominator r := (graphCharacteristic_transport p x).trans hPx
    have hFB : diagonalCofactor B o=stieltjesNumerator r w := (graphRootCofactor_transport p x).trans hFx
    rw [hPB,hFB] at heq
    have hdeg : A.charpoly.natDegree=(stieltjesDenominator r).natDegree := by
      rw [Matrix.charpoly_natDegree_eq_dim,presentation_vertex_card p,stieltjesDenominator_natDegree]
    have hp := full_degree_fraction_unique _ _ _ _ (stieltjesDenominator_monic r)
      (Matrix.charpoly_monic A) hdeg (full_stieltjes_pair_coprime r w hr hpos hw hm) heq
    exact (real_located_response_iff_pair p ell y r w hr hpos hw hm).mpr ⟨hp.1.symm,hp.2.symm⟩
  · intro h
    have hy := real_located_response_forces_positive hG p ell y r w hr hpos hw hm h
    exact (located_continuous_iff_response hG p ell ⟨y,hy⟩ r w hr hpos hw hm).mpr h

abbrev RealLocatedContinuousFiber {n : ℕ} (o ell : V) (r w : Fin (n+1) → ℝ) :=
  {y : GraphRates G // HasLocatedContinuousRootOutput o ell y r w}

def realLocatedContinuousEquivResponse {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    RealLocatedContinuousFiber (G := G) o ell r w ≃ RealLocatedFiber (G := G) o ell r w where
  toFun y := ⟨y.val,(real_located_continuous_iff_response hG p ell y.val r w hr hpos hw hm).mp y.property⟩
  invFun y := ⟨y.val,(real_located_continuous_iff_response hG p ell y.val r w hr hpos hw hm).mpr y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact exhaustive classification of ALL real models from actual histories,
not from artificially supplied internal coefficient data or sign constraints. -/
theorem real_located_continuous_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Nonempty (RealLocatedContinuousFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
    Finite (RealLocatedContinuousFiber (G := G) o ell r w) ∧
      Nat.card (RealLocatedContinuousFiber (G := G) o ell r w)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) ∧
      ∀ y : RealLocatedContinuousFiber (G := G) o ell r w,PositiveGraphRates y.val ∧ locatedGraphJacobian p ell y.val ≠ 0 := by
  let E := realLocatedContinuousEquivResponse hG p ell r w hr hpos hw hm
  obtain ⟨hf,hc⟩ := real_located_fiber_exact_card hG p ell r w hr hpos hw hm
  letI := hf
  exact ⟨⟨E.trans (realLocatedRecursiveEquiv hG p ell r w hr hpos hw hm)⟩,
    Finite.of_injective E E.injective,(Nat.card_congr E).trans hc,
    fun y => real_located_full_response_positive_regular hG p ell y.val r w hr hpos hw hm (E y).property⟩

abbrev RealUnknownLeakContinuousFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  Σ ell : V,RealLocatedContinuousFiber (G := G) o ell r w

theorem real_unknown_leak_continuous_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Finite (RealUnknownLeakContinuousFiber (G := G) o r w) ∧
      Nat.card (RealUnknownLeakContinuousFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ)) := by
  have hc (ell : V) := real_located_continuous_fiber_exact_card hG p ell r w hr hpos hw hm
  letI : ∀ ell : V,Finite (RealLocatedContinuousFiber (G := G) o ell r w) := fun ell => (hc ell).2.1
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_sigma]
  simp only [fun ell => (hc ell).2.2.1,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]

/-- Independent graph input; all sites and every initially signed real
continuous-output competitor are included in the classified physical fiber. -/
theorem finite_graph_all_real_leak_ODE_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      (∀ ell : V,Nonempty (RealLocatedContinuousFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
        Finite (RealLocatedContinuousFiber (G := G) o ell r w) ∧
        Nat.card (RealLocatedContinuousFiber (G := G) o ell r w)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) ∧
        ∀ y : RealLocatedContinuousFiber (G := G) o ell r w,PositiveGraphRates y.val ∧ locatedGraphJacobian p ell y.val ≠ 0) ∧
      Finite (RealUnknownLeakContinuousFiber (G := G) o r w) ∧
      Nat.card (RealUnknownLeakContinuousFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ)) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  exact ⟨p,fun ell => real_located_continuous_fiber_exact_card hG p ell r w hr hpos hw hm,
    real_unknown_leak_continuous_exact_card hG p r w hr hpos hw hm⟩

end HydrologyTree
