import HydrologyTree.LocatedLeakDynamics

/-! All-input non-identifiability of the single leak location from collocated
state observations. Actual trajectories and existence are included. This is NOT
an assertion about the outflow at a different leakage vertex or cross responses. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Moving the leak preserves every actual zero-initial collocated history at
any fixed inlet/observer, without a simple-pole or full-mode assumption. -/
theorem leak_relocation_same_actual_outputs (hG : G.IsTree) (ell ell' : V)
    (y : PositiveGraphRateSpace G) (o : V) (u : ℝ → ℝ)
    (z q : ℝ → V → ℝ)
    (hz : IsLocatedGraphSolution o ell y.val u z)
    (hq : IsLocatedGraphSolution o ell' (relocatePositiveLeak hG ell ell' y).val u q)
    (hz0 : z 0=0) (hq0 : q 0=0) : ∀ s : ℝ, z s o=q s o := by
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell ell' y
  have hn : ∀ v, h v ≠ 0 := fun v => ne_of_gt (hh v)
  let E := normalizedGaugeTrajectory h hn o
  have hE : IsLocatedGraphSolution o ell' (relocatePositiveLeak hG ell ell' y).val u (E z) := by
    change IsForcedMatrixSolution _ _ _ _
    rw [hM]
    exact (normalizedGauge_solution_iff h hn o _ u z).mp hz
  have he0 : E z 0=0 := (normalizedGauge_zero_iff h hn o z 0).mpr hz0
  have he : E z=q := forcedMatrixSolution_unique _ (Pi.single o 1) u _ q 0 hE hq (he0.trans hq0.symm)
  intro s
  have ho := congrArg (fun f : ℝ → V → ℝ => f s o) he
  simpa only [E,normalizedGaugeTrajectory_root] using ho

/-- Non-identifiability is not a vacuous universal predicate: the actual global
classical solutions exist uniquely for every continuous forcing, before and after
relocation, and agree at the observer for every real time. -/
theorem leak_location_all_input_indistinguishability (hG : G.IsTree) (ell ell' : V)
    (y : PositiveGraphRateSpace G) :
    ∀ (o : V) (u : ℝ → ℝ), Continuous u →
      ∃ (z q : ℝ → V → ℝ),
        IsLocatedGraphSolution o ell y.val u z ∧ z 0=0 ∧
        IsLocatedGraphSolution o ell' (relocatePositiveLeak hG ell ell' y).val u q ∧ q 0=0 ∧
        (∀ s : ℝ, z s o=q s o) ∧
        (∀ z', IsLocatedGraphSolution o ell y.val u z' → z' 0=0 → z'=z) ∧
        (∀ q', IsLocatedGraphSolution o ell' (relocatePositiveLeak hG ell ell' y).val u q' → q' 0=0 → q'=q) := by
  intro o u hu
  obtain ⟨z,hz,huZ⟩ := located_forced_ODE_existsUnique hG o ell y u hu 0 0
  obtain ⟨q,hq,huQ⟩ := located_forced_ODE_existsUnique hG o ell' (relocatePositiveLeak hG ell ell' y) u hu 0 0
  exact ⟨z,q,hz.1,hz.2,hq.1,hq.2,
    leak_relocation_same_actual_outputs hG ell ell' y o u z q hz.1 hq.1 hz.2 hq.2,
    fun z' hz' hz0 => huZ z' ⟨hz',hz0⟩,fun q' hq' hq0 => huQ q' ⟨hq',hq0⟩⟩

abbrev UnknownLeakContinuousFiber {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :=
  Σ ell : V, PositiveLocatedContinuousFiber (G := G) o ell r w

/-- The complete unknown-location ambiguity count concerns actual trajectories
for every continuous input, not just equality of sampled or symbolic responses. -/
theorem unknown_leak_continuous_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    Finite (UnknownLeakContinuousFiber (G := G) o r w) ∧
      Nat.card (UnknownLeakContinuousFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ)) := by
  have hc (ell : V) := located_continuous_fiber_exact_card hG p ell r w hr hpos hw hm
  letI : ∀ ell : V, Finite (PositiveLocatedContinuousFiber (G := G) o ell r w) := fun ell => (hc ell).2.1
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_sigma]
  simp only [fun ell => (hc ell).2.2,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]

/-- Independent graph inputs construct their own presentation. All leak sites
and the unknown-site count are classified from actual continuous state histories. -/
theorem finite_graph_all_leak_ODE_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V)
    (hN : Fintype.card V=n+1) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0<r i) (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      (∀ ell : V, Nonempty (PositiveLocatedContinuousFiber (G := G) o ell r w ≃ RecursivePoleAllocations p.tree) ∧
        Finite (PositiveLocatedContinuousFiber (G := G) o ell r w) ∧
        Nat.card (PositiveLocatedContinuousFiber (G := G) o ell r w)=
          n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ)) ∧
      Finite (UnknownLeakContinuousFiber (G := G) o r w) ∧
      Nat.card (UnknownLeakContinuousFiber (G := G) o r w)=
        Fintype.card V*(n.factorial/(∏ e : Fin n, subtreeVertexCount p.tree e.succ)) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  exact ⟨p,fun ell => located_continuous_fiber_exact_card hG p ell r w hr hpos hw hm,
    unknown_leak_continuous_fiber_exact_card hG p r w hr hpos hw hm⟩

end HydrologyTree
