import HydrologyTree.GraphODETransport
import HydrologyTree.GraphResponseClassification
import HydrologyTree.FullRootLeakTheory
import HydrologyTree.PhysicalMinimumEnergy

/-! Actual continuous-time graph output classification, reachability,
observability and optimal control. A presentation only mediates proved
bijections; the statements use the independent graph's rates and state ODE. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def HasGraphContinuousDischargeOutput {n : ℕ} (o : V) (y : GraphRates G) (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ (u : ℝ → ℝ), Continuous u → ∀ z : ℝ → V → ℝ,
    IsGraphForcedSolution o y u z → z 0=0 → ∀ s : ℝ, 0 ≤ s →
      y.1*z s o=stieltjesLeak r w*(∑ i, w i*scalarForcedSolution (r i) u 0 0 s)

lemma graph_continuous_discharge_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (r w : Fin (n+1) → ℝ) :
    HasGraphContinuousDischargeOutput o (graphRateEquiv p x) r w ↔
      HasFullContinuousDischargeOutput p.tree x r w := by
  constructor
  · intro h u hu q hq hq0 s hs
    have hODE : IsGraphForcedSolution o (graphRateEquiv p x) u ((graphTrajectoryEquiv p).symm q) := by
      apply (graph_forced_solution_transport p x u _).mpr
      simpa only [Equiv.apply_symm_apply] using hq
    have h0 : (graphTrajectoryEquiv p).symm q 0=0 := by
      apply (graph_trajectory_zero_iff p _ 0).mp
      simpa only [Equiv.apply_symm_apply] using hq0
    have hh := h u hu _ hODE h0 s hs
    simpa only [graphRateEquiv_leak,graphTrajectoryEquiv_symm_root] using hh
  · intro h u hu z hz hz0 s hs
    have hh := h u hu (graphTrajectoryEquiv p z) ((graph_forced_solution_transport p x u z).mp hz)
      ((graph_trajectory_zero_iff p z 0).mpr hz0) s hs
    simpa only [graphRateEquiv_leak,graphTrajectoryEquiv_root] using hh

/-- Output histories determine the full graph response and hence all previously
proved fiber statements, without additional state or coefficient observations. -/
theorem graph_continuous_discharge_iff_response {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    HasGraphContinuousDischargeOutput o y r w ↔ HasGraphStieltjesResponse o y r w := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [graph_continuous_discharge_transport,continuous_discharge_output_iff_response p.tree x r w hr hpos hw hm,
    graph_response_transport]

abbrev GraphContinuousDischargeFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  {y : GraphRates G // HasGraphContinuousDischargeOutput o y r w}

def graphContinuousFiberEquivResponse {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    GraphContinuousDischargeFiber (G := G) o r w ≃ GraphResponseFiber (G := G) o r w where
  toFun y := ⟨y.val,(graph_continuous_discharge_iff_response p y.val r w hr hpos hw hm).mp y.property⟩
  invFun y := ⟨y.val,(graph_continuous_discharge_iff_response p y.val r w hr hpos hw hm).mpr y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem graph_continuous_fiber_exact_card {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (GraphContinuousDischargeFiber (G := G) o r w) ∧
      Nat.card (GraphContinuousDischargeFiber (G := G) o r w)=n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) := by
  obtain ⟨hf,hc⟩ := graph_response_fiber_exact_card p r w hr hpos hw hm
  letI := hf
  let E := graphContinuousFiberEquivResponse p r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- Signed finite-horizon controllability of the actual independent graph system. -/
theorem graph_full_response_controllable {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hy : HasGraphStieltjesResponse o y r w) (T : ℝ) (hT : 0 < T) (z0 z1 : V → ℝ) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      ∃! z : ℝ → V → ℝ, IsGraphForcedSolution o y u z ∧ z 0=z0 ∧ z T=z1 := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  have hx := (graph_response_transport p x r w).mp hy
  obtain ⟨u,hu,hsol⟩ := real_full_response_controllable p.tree x r w hr hpos hw hm hx T hT
    (graphStateEquiv p z0) (graphStateEquiv p z1)
  exact ⟨u,hu,(graph_two_endpoint_existsUnique_iff p x u T z0 z1).mpr hsol⟩

/-- The sharp energy identity and equality case apply to every actual graph
trajectory meeting the endpoints; no modal constraints are imposed on the user. -/
theorem graph_full_response_minimum_energy {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hy : HasGraphStieltjesResponse o y r w) (T : ℝ) (hT : 0 < T) (z0 z1 : V → ℝ) :
    ∃ u0 : ℝ → ℝ, Continuous u0 ∧
      (∃! z : ℝ → V → ℝ, IsGraphForcedSolution o y u0 z ∧ z 0=z0 ∧ z T=z1) ∧
      ∀ u : ℝ → ℝ, Continuous u → ∀ z : ℝ → V → ℝ,
        IsGraphForcedSolution o y u z → z 0=z0 → z T=z1 →
        controlEnergy T u=controlEnergy T u0+controlEnergy T (fun s => u s-u0 s) ∧
        controlEnergy T u0 ≤ controlEnergy T u ∧
        (controlEnergy T u=controlEnergy T u0 ↔ ∀ s ∈ Set.Icc 0 T, u s=u0 s) := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  have hx := (graph_response_transport p x r w).mp hy
  obtain ⟨u0,hu0,hsol,hmin⟩ := real_full_response_minimum_energy_control p.tree x r w hr hpos hw hm hx
    T hT (graphStateEquiv p z0) (graphStateEquiv p z1)
  refine ⟨u0,hu0,(graph_two_endpoint_existsUnique_iff p x u0 T z0 z1).mpr hsol,?_⟩
  intro u hu z hz h0 h1
  exact hmin u hu (graphTrajectoryEquiv p z) ((graph_forced_solution_transport p x u z).mp hz)
    ((graph_trajectory_endpoint_iff p z 0 z0).mpr h0) ((graph_trajectory_endpoint_iff p z T z1).mpr h1)

end HydrologyTree
