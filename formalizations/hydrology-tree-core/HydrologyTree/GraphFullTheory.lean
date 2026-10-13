import HydrologyTree.GraphDynamicalClassification
import HydrologyTree.GraphCoefficientJacobian
import HydrologyTree.GraphMassBalance

/-! Presentation-free hypotheses for the original graph's actual full-response
fibers, continuous ODE histories and finite-time system properties. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The actual graph coefficient derivative is nonsingular at every full target
realization; sign or regularity restrictions on competitors are not assumptions. -/
theorem graph_full_response_regular {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (y : GraphResponseFiber (G := G) o r w) :
    graphCanonicalJacobian p y.val ≠ 0 := by
  rw [graphCanonicalJacobian_transport]
  exact (real_full_response_forces_positive_regular p.tree
    ((graphResponseFiberEquiv p r w) y).val r w hr hpos hw hm
      ((graphResponseFiberEquiv p r w) y).property).2

/-- Equality of root output on any nonempty open interval determines the entire
actual graph state trajectory under the same forcing and model. -/
theorem graph_full_response_observable {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hy : HasGraphStieltjesResponse o y r w)
    (u : ℝ → ℝ) (z q : ℝ → V → ℝ)
    (hz : IsGraphForcedSolution o y u z) (hq : IsGraphForcedSolution o y u q)
    (a b : ℝ) (hab : a<b) (hout : ∀ s ∈ Set.Ioo a b, z s o=q s o) : z=q := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  apply (graphTrajectoryEquiv p).injective
  apply real_full_response_trajectory_observable p.tree x r w hr hpos hw hm
    ((graph_response_transport p x r w).mp hy) u
    (graphTrajectoryEquiv p z) (graphTrajectoryEquiv p q)
    ((graph_forced_solution_transport p x u z).mp hz)
    ((graph_forced_solution_transport p x u q).mp hq) a b hab
  simpa only [graphTrajectoryEquiv_root] using hout

/-- Full actual graph trajectory-fiber classification. The presentation is
constructed from G.IsTree and the cardinality, not required as extra data. -/
theorem finite_graph_continuous_fiber_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V)
    (hN : Fintype.card V=n+1) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      Nonempty (GraphContinuousDischargeFiber (G := G) o r w ≃ RecursivePoleAllocations p.tree) ∧
      Finite (GraphContinuousDischargeFiber (G := G) o r w) ∧
      Nat.card (GraphContinuousDischargeFiber (G := G) o r w)=
        n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) ∧
      ∀ y : GraphContinuousDischargeFiber (G := G) o r w,
        PositiveGraphRates y.val ∧ graphCanonicalJacobian p y.val ≠ 0 := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  obtain ⟨hf,hc⟩ := graph_continuous_fiber_exact_card p r w hr hpos hw hm
  refine ⟨p,⟨(graphContinuousFiberEquivResponse p r w hr hpos hw hm).trans
    (graphResponseRecursiveEquiv p r w hr hpos hw hm)⟩,hf,hc,?_⟩
  intro y
  let v := graphContinuousFiberEquivResponse p r w hr hpos hw hm y
  exact ⟨graph_full_response_positive p r w hr hpos hw hm v,
    graph_full_response_regular p r w hr hpos hw hm v⟩

/-- A presentation built from the graph yields actual well-posedness, arbitrary
positive-horizon signed steering and full finite-window trajectory observability. -/
theorem finite_graph_full_dynamical_properties {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V)
    (hN : Fintype.card V=n+1) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (y : GraphContinuousDischargeFiber (G := G) o r w) :
    PositiveGraphRates y.val ∧
    (∀ u : ℝ → ℝ, Continuous u → ∀ (a : ℝ) (z0 : V → ℝ),
      ∃! z : ℝ → V → ℝ, IsGraphForcedSolution o y.val u z ∧ z a=z0) ∧
    (∀ T : ℝ, 0<T → ∀ z0 z1 : V → ℝ,
      ∃ u : ℝ → ℝ, Continuous u ∧
      ∃! z : ℝ → V → ℝ, IsGraphForcedSolution o y.val u z ∧ z 0=z0 ∧ z T=z1) ∧
    (∀ (u : ℝ → ℝ) (z q : ℝ → V → ℝ), IsGraphForcedSolution o y.val u z →
      IsGraphForcedSolution o y.val u q → ∀ a b : ℝ, a<b →
      (∀ s ∈ Set.Ioo a b, z s o=q s o) → z=q) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  have hy := (graph_continuous_discharge_iff_response p y.val r w hr hpos hw hm).mp y.property
  have hp := graph_full_response_positive p r w hr hpos hw hm ⟨y.val,hy⟩
  refine ⟨hp,?_,?_,?_⟩
  · exact fun u hu a z0 => graph_forced_ODE_existsUnique p y.val hp u hu a z0
  · exact fun T hT z0 z1 => graph_full_response_controllable p y.val r w hr hpos hw hm hy T hT z0 z1
  · exact fun u z q hz hq a b hab ho => graph_full_response_observable p y.val r w hr hpos hw hm hy u z q hz hq a b hab ho

end HydrologyTree
