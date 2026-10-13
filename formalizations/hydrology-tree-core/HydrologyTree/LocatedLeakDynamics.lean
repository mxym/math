import HydrologyTree.LocatedLeakODE
import HydrologyTree.GraphFullTheory

/-! Actual global ODE solutions, finite-window observability, signed reachability
and exact energy rigidity with leakage away from the inlet/observer. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The input-normalized gauge transports actual initial-value solutions and
uniqueness without changing the scalar input or observed coordinate. -/
theorem gauge_initial_existsUnique (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (u : ℝ → ℝ) (a : ℝ) (z0 : V → ℝ)
    (he : ∃! q : ℝ → V → ℝ, IsForcedMatrixSolution (diagonalGauge h A) (Pi.single o 1) u q ∧
      q a=normalizedGaugeState h hh o z0) :
    ∃! z : ℝ → V → ℝ, IsForcedMatrixSolution A (Pi.single o 1) u z ∧ z a=z0 := by
  let E := normalizedGaugeTrajectory h hh o
  obtain ⟨q,hq,hu⟩ := he
  have hsol : IsForcedMatrixSolution A (Pi.single o 1) u (E.symm q) := by
    apply (normalizedGauge_solution_iff h hh o A u _).mpr
    simpa only [E,Equiv.apply_symm_apply] using hq.1
  have h0 : E.symm q a=z0 := by
    apply (normalizedGauge_endpoint_iff h hh o _ a z0).mp
    simpa only [E,Equiv.apply_symm_apply] using hq.2
  refine ⟨E.symm q,⟨hsol,h0⟩,?_⟩
  intro z hz
  apply E.injective
  rw [Equiv.apply_symm_apply]
  exact hu _ ⟨(normalizedGauge_solution_iff h hh o A u z).mp hz.1,
    (normalizedGauge_endpoint_iff h hh o z a z0).mpr hz.2⟩

/-- Every positive tree model with arbitrary leak site and arbitrary inlet has
a unique actual global classical state solution for each continuous input. -/
theorem located_forced_ODE_existsUnique (hG : G.IsTree) (o ell : V)
    (y : PositiveGraphRateSpace G) (u : ℝ → ℝ) (hu : Continuous u) (a : ℝ) (z0 : V → ℝ) :
    ∃! z : ℝ → V → ℝ, IsLocatedGraphSolution o ell y.val u z ∧ z a=z0 := by
  let p := finiteGraphPresentation G hG o
  let y0 := relocatePositiveLeak hG ell o y
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  apply gauge_initial_existsUnique h hn o (graphCompartmentMatrix G ell y.val) u a z0
  have he := graph_forced_ODE_existsUnique p y0.val y0.property u hu a (normalizedGaugeState h hn o z0)
  change (∃! q : ℝ → V → ℝ, IsForcedMatrixSolution _ (Pi.single o 1) u q ∧ q a=_) at he
  rwa [hM] at he

/-- For full targets, the actual state is determined by root measurements on
any nonempty open interval, even though leakage is at a different vertex. -/
theorem located_full_response_observable {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : PositiveGraphRateSpace G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) (hy : HasLocatedStieltjesResponse o ell y.val r w)
    (u : ℝ → ℝ) (z q : ℝ → V → ℝ)
    (hz : IsLocatedGraphSolution o ell y.val u z) (hq : IsLocatedGraphSolution o ell y.val u q)
    (a b : ℝ) (hab : a<b) (hout : ∀ s ∈ Set.Ioo a b, z s o=q s o) : z=q := by
  let y0 := relocatePositiveLeak hG ell o y
  have hR : HasGraphStieltjesResponse o y0.val r w :=
    (located_response_relocate hG o ell o y r w).mp hy
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  let E := normalizedGaugeTrajectory h hn o
  have hz' : IsGraphForcedSolution o y0.val u (E z) := by
    change IsForcedMatrixSolution _ _ _ _
    rw [hM]
    exact (normalizedGauge_solution_iff h hn o _ u z).mp hz
  have hq' : IsGraphForcedSolution o y0.val u (E q) := by
    change IsForcedMatrixSolution _ _ _ _
    rw [hM]
    exact (normalizedGauge_solution_iff h hn o _ u q).mp hq
  apply E.injective
  apply graph_full_response_observable p y0.val r w hr hpos hw hm hR u (E z) (E q) hz' hq' a b hab
  simpa only [E,normalizedGaugeTrajectory_root] using hout

/-- Signed continuous controls achieve arbitrary actual state endpoints at any
T>0 with arbitrary positive leakage position; no state rescaling is hidden in
those endpoints. The proof transports endpoints explicitly and back. -/
theorem located_full_response_controllable {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : PositiveGraphRateSpace G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) (hy : HasLocatedStieltjesResponse o ell y.val r w)
    (T : ℝ) (hT : 0<T) (z0 z1 : V → ℝ) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      ∃! z : ℝ → V → ℝ, IsLocatedGraphSolution o ell y.val u z ∧ z 0=z0 ∧ z T=z1 := by
  let y0 := relocatePositiveLeak hG ell o y
  have hR : HasGraphStieltjesResponse o y0.val r w :=
    (located_response_relocate hG o ell o y r w).mp hy
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  obtain ⟨u,hu,hsol⟩ := graph_full_response_controllable p y0.val r w hr hpos hw hm hR T hT
    (normalizedGaugeState h hn o z0) (normalizedGaugeState h hn o z1)
  refine ⟨u,hu,(normalizedGauge_endpoints_existsUnique_iff h hn o _ u T z0 z1).mpr ?_⟩
  change (∃! q : ℝ → V → ℝ, IsForcedMatrixSolution _ _ _ _ ∧ q 0=_ ∧ q T=_) at hsol
  rwa [hM] at hsol

/-- Exact energy decomposition and complete equality classification for actual
alternate-leak endpoint control. The same physical scalar input is used before
and after the gauge; this is not optimization in a substituted input model. -/
theorem located_full_response_minimum_energy {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : PositiveGraphRateSpace G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) (hy : HasLocatedStieltjesResponse o ell y.val r w)
    (T : ℝ) (hT : 0<T) (z0 z1 : V → ℝ) :
    ∃ u0 : ℝ → ℝ, Continuous u0 ∧
      (∃! z : ℝ → V → ℝ, IsLocatedGraphSolution o ell y.val u0 z ∧ z 0=z0 ∧ z T=z1) ∧
      ∀ u : ℝ → ℝ, Continuous u → ∀ z : ℝ → V → ℝ,
        IsLocatedGraphSolution o ell y.val u z → z 0=z0 → z T=z1 →
        controlEnergy T u=controlEnergy T u0+controlEnergy T (fun s => u s-u0 s) ∧
        controlEnergy T u0 ≤ controlEnergy T u ∧
        (controlEnergy T u=controlEnergy T u0 ↔ ∀ s ∈ Set.Icc 0 T, u s=u0 s) := by
  let y0 := relocatePositiveLeak hG ell o y
  have hR : HasGraphStieltjesResponse o y0.val r w :=
    (located_response_relocate hG o ell o y r w).mp hy
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  obtain ⟨u0,hu0,hsol,hmin⟩ := graph_full_response_minimum_energy p y0.val r w hr hpos hw hm hR T hT
    (normalizedGaugeState h hn o z0) (normalizedGaugeState h hn o z1)
  refine ⟨u0,hu0,?_,?_⟩
  · apply (normalizedGauge_endpoints_existsUnique_iff h hn o _ u0 T z0 z1).mpr
    change (∃! q : ℝ → V → ℝ, IsForcedMatrixSolution _ _ _ _ ∧ q 0=_ ∧ q T=_) at hsol
    rwa [hM] at hsol
  · intro u hu z hz h0 h1
    have hODE : IsGraphForcedSolution o y0.val u (normalizedGaugeTrajectory h hn o z) := by
      change IsForcedMatrixSolution _ _ _ _
      rw [hM]
      exact (normalizedGauge_solution_iff h hn o _ u z).mp hz
    exact hmin u hu _ hODE ((normalizedGauge_endpoint_iff h hn o z 0 z0).mpr h0)
      ((normalizedGauge_endpoint_iff h hn o z T z1).mpr h1)

end HydrologyTree
