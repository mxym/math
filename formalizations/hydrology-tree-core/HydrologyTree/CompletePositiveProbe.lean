import HydrologyTree.PuncturedJetData
import HydrologyTree.MixedInputJets

/-! A complete theoretical identification protocol: low-order all-node jets
reduce arbitrary real competitors to finitely many leakage sites; one adaptive
positive rational mixed probe then identifies the true site and all rates.
The probe is not claimed universal, sparse, or robust to measurement noise. -/
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Choose a single bilinear probe that separates all actual candidate matrices
remaining after the diagonal experiments, not only the true model from one rival. -/
theorem all_node_fiber_has_positive_probe {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    ∃ b c : V → ℕ,Function.Injective (fun z : AllNodeJetFiber o x.val =>
      matrixProbeValue (graphCompartmentMatrix G z.1 z.2.val)
        (fun v => boundedProbeWeight (b v)) (fun v => boundedProbeWeight (c v))) := by
  classical
  letI : Finite (AllNodeJetFiber o x.val) := (all_node_two_jet_exact_card hG p x).1
  letI : Fintype (AllNodeJetFiber o x.val) := Fintype.ofFinite _
  exact exists_positive_rational_matrix_probe _ (allNodeJetFiber_matrix_injective hG p x)

/-- Only 2N-1 low-order scalar coefficients and one further mixed coefficient
suffice. The leak position and all initially real competing rates are determined.
The weightings may depend on the identified finite candidate family. -/
theorem positive_probe_identifies_site_and_rates {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) (v0 : V) :
    ∃ b c : V → ℕ,∀ (ell : V) (y : GraphRates G),
      SamePuncturedDiagonalJets v0 (graphCompartmentMatrix G ell y) (graphCompartmentMatrix G o x.val) →
      matrixProbeValue (graphCompartmentMatrix G ell y)
        (fun v => boundedProbeWeight (b v)) (fun v => boundedProbeWeight (c v)) =
      matrixProbeValue (graphCompartmentMatrix G o x.val)
        (fun v => boundedProbeWeight (b v)) (fun v => boundedProbeWeight (c v)) →
      ell=o ∧ y=x.val := by
  obtain ⟨b,c,hsep⟩ := all_node_fiber_has_positive_probe hG p x
  refine ⟨b,c,?_⟩
  intro ell y hy hval
  have hj := graph_punctured_jets_complete (leakRootPresentation hG p v0) ell o y x.val hy
  let z : AllNodeJetFiber o x.val := ⟨ell,⟨y,hj⟩⟩
  let z0 : AllNodeJetFiber o x.val := ⟨o,⟨x.val,rfl⟩⟩
  have he : z=z0 := hsep hval
  exact ⟨congrArg Sigma.fst he,congrArg (fun a : AllNodeJetFiber o x.val => a.2.val) he⟩

/-- The extra coefficient is the actual second derivative of a nonnegative
constant mixed-input experiment, with a strictly positive weighted state output.
All chosen weights are explicitly rational numbers in (1,2). -/
theorem actual_positive_mixed_probe_identification {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    ∃ b c : V → ℕ,
      (∃! z : ℝ → V → ℝ,
        IsForcedMatrixSolution (graphCompartmentMatrix G o x.val)
          (fun v => boundedProbeWeight (b v)) (fun _ => 1) z ∧ z 0=0) ∧
      ∀ (ell : V) (y : GraphRates G),SameAllNodeStepJets o ell x.val y →
      ∀ z q : ℝ → V → ℝ,
        IsForcedMatrixSolution (graphCompartmentMatrix G o x.val)
          (fun v => boundedProbeWeight (b v)) (fun _ => 1) z → z 0=0 →
        IsForcedMatrixSolution (graphCompartmentMatrix G ell y)
          (fun v => boundedProbeWeight (b v)) (fun _ => 1) q → q 0=0 →
        iteratedDeriv 2 (fun s => ∑ v,boundedProbeWeight (c v)*z s v) 0 =
          iteratedDeriv 2 (fun s => ∑ v,boundedProbeWeight (c v)*q s v) 0 →
        ell=o ∧ y=x.val := by
  obtain ⟨b,c,hid⟩ := positive_probe_identifies_site_and_rates hG p x o
  refine ⟨b,c,positive_graph_mixed_step_existsUnique hG o x _,?_⟩
  intro ell y hy z q hz hz0 hq hq0 he
  apply hid ell y
  · have hj := (all_node_step_jets_iff_moments hG p ell x y).mp hy
    exact ⟨(fun v => congrArg (fun a : (V → ℝ) × (V → ℝ) => a.1 v) hj),
      (fun v _ => congrArg (fun a : (V → ℝ) × (V → ℝ) => a.2 v) hj)⟩
  · rw [mixed_step_second_derivative hz hz0,mixed_step_second_derivative hq hq0] at he
    exact he.symm

end HydrologyTree
