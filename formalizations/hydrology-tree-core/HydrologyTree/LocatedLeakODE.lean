import HydrologyTree.GaugeODETransport
import HydrologyTree.LocatedLeakFiber
import HydrologyTree.GraphODETransport
import HydrologyTree.ContinuousOutputFiber

/-! Actual continuous-time state-output fibers for arbitrary leak positions.
Normalization at the fixed inlet keeps the input and observation unchanged.
Full response equivalence is proved in BOTH directions on actual trajectories. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev IsLocatedGraphSolution (o ell : V) (y : GraphRates G) (u : ℝ → ℝ) (z : ℝ → V → ℝ) : Prop :=
  IsForcedMatrixSolution (graphCompartmentMatrix G ell y) (Pi.single o 1) u z

def HasMatrixContinuousRootOutput {n : ℕ} (A : Matrix V V ℝ) (o : V)
    (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Continuous u → ∀ z : ℝ → V → ℝ,
    IsForcedMatrixSolution A (Pi.single o 1) u z → z 0=0 → ∀ s : ℝ, 0≤s →
      z s o=∑ i, w i*scalarForcedSolution (r i) u 0 0 s

abbrev HasLocatedContinuousRootOutput {n : ℕ} (o ell : V) (y : GraphRates G)
    (r w : Fin (n+1) → ℝ) : Prop :=
  HasMatrixContinuousRootOutput (graphCompartmentMatrix G ell y) o r w

/-- Diagonal similarity gives the same actual histories under the SAME input,
with zero initial state; it is not merely a resolvent comparison. -/
theorem gauge_continuous_root_iff {n : ℕ} (h : V → ℝ) (hh : ∀ v, h v ≠ 0)
    (A : Matrix V V ℝ) (o : V) (r w : Fin (n+1) → ℝ) :
    HasMatrixContinuousRootOutput A o r w ↔ HasMatrixContinuousRootOutput (diagonalGauge h A) o r w := by
  let E := normalizedGaugeTrajectory h hh o
  constructor
  · intro hA u hu q hq hq0 s hs
    have hsol : IsForcedMatrixSolution A (Pi.single o 1) u (E.symm q) := by
      apply (normalizedGauge_solution_iff h hh o A u _).mpr
      simpa only [E,Equiv.apply_symm_apply] using hq
    have hzero : E.symm q 0=0 := by
      apply (normalizedGauge_zero_iff h hh o _ 0).mp
      simpa only [E,Equiv.apply_symm_apply] using hq0
    have hout := hA u hu _ hsol hzero s hs
    simpa only [E,normalizedGaugeTrajectory_symm_root] using hout
  · intro hB u hu z hz hz0 s hs
    have he := hB u hu (E z) ((normalizedGauge_solution_iff h hh o A u z).mp hz)
      ((normalizedGauge_zero_iff h hh o z 0).mpr hz0) s hs
    simpa only [E,normalizedGaugeTrajectory_root] using he

lemma graph_continuous_root_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (r w : Fin (n+1) → ℝ) :
    HasLocatedContinuousRootOutput o o (graphRateEquiv p x) r w ↔
      HasFullContinuousRootOutput p.tree x r w := by
  constructor
  · intro h u hu q hq hq0 s hs
    have hODE : IsGraphForcedSolution o (graphRateEquiv p x) u ((graphTrajectoryEquiv p).symm q) := by
      apply (graph_forced_solution_transport p x u _).mpr
      simpa only [Equiv.apply_symm_apply] using hq
    have h0 : (graphTrajectoryEquiv p).symm q 0=0 := by
      apply (graph_trajectory_zero_iff p _ 0).mp
      simpa only [Equiv.apply_symm_apply] using hq0
    have he := h u hu _ hODE h0 s hs
    simpa only [graphTrajectoryEquiv_symm_root] using he
  · intro h u hu z hz hz0 s hs
    have he := h u hu (graphTrajectoryEquiv p z) ((graph_forced_solution_transport p x u z).mp hz)
      ((graph_trajectory_zero_iff p z 0).mpr hz0) s hs
    simpa only [graphTrajectoryEquiv_root] using he

/-- Root-state histories, rather than discharge at a possibly different vertex. -/
theorem graph_root_continuous_iff_response {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    HasLocatedContinuousRootOutput o o y r w ↔ HasGraphStieltjesResponse o y r w := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [graph_continuous_root_transport,continuous_root_output_iff_response p.tree x r w hr hpos hw hm,
    graph_response_transport]

/-- Every positive alternate-leak model: exact continuous-history/resolvent
identification, with both directions and no unproved existence premise. -/
theorem located_continuous_iff_response {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : PositiveGraphRateSpace G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    HasLocatedContinuousRootOutput o ell y.val r w ↔ HasLocatedStieltjesResponse o ell y.val r w := by
  let y0 := relocatePositiveLeak hG ell o y
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell o y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  have he : HasLocatedContinuousRootOutput o ell y.val r w ↔
      HasLocatedContinuousRootOutput o o y0.val r w := by
    change HasMatrixContinuousRootOutput _ _ _ _ ↔ HasMatrixContinuousRootOutput _ _ _ _
    rw [hM]
    exact gauge_continuous_root_iff h hn _ o r w
  rw [he,graph_root_continuous_iff_response p y0.val r w hr hpos hw hm,
    ← located_response_at_root]
  exact (located_response_relocate hG o ell o y r w).symm

abbrev PositiveLocatedContinuousFiber {n : ℕ} (o ell : V) (r w : Fin (n+1) → ℝ) :=
  {y : PositiveGraphRateSpace G // HasLocatedContinuousRootOutput o ell y.val r w}

def locatedContinuousFiberEquivResponse {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    PositiveLocatedContinuousFiber (G := G) o ell r w ≃ PositiveLocatedFiber (G := G) o ell r w where
  toFun y := ⟨y.val,(located_continuous_iff_response hG p ell y.val r w hr hpos hw hm).mp y.property⟩
  invFun y := ⟨y.val,(located_continuous_iff_response hG p ell y.val r w hr hpos hw hm).mpr y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete finite classification for actual continuous-input state histories
at a fixed inlet/observer and any leak site. Parameters are actual graph rates. -/
theorem located_continuous_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    Nonempty (PositiveLocatedContinuousFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
    Finite (PositiveLocatedContinuousFiber (G := G) o ell r w) ∧
      Nat.card (PositiveLocatedContinuousFiber (G := G) o ell r w)=
        n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ) := by
  let E := locatedContinuousFiberEquivResponse hG p ell r w hr hpos hw hm
  obtain ⟨hf,hc⟩ := located_positive_fiber_exact_card hG p ell r w hr hpos hw hm
  letI := hf
  exact ⟨⟨E.trans (locatedPositiveRecursiveEquiv hG p ell r w hr hpos hw hm)⟩,
    Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

end HydrologyTree
