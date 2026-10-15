import HydrologyTree.AllNodeJetClassification
import HydrologyTree.ConstantInputJets
import HydrologyTree.LeakLocationIdentifiability

/-! Complete actual-experiment semantics for the short-time classification.
Experiments use continuous constant forcing and actual zero-initial classical
trajectories. Existence is included, preventing vacuous trajectory predicates. -/
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every original node, compare the second and third derivatives of its
own output under a unit input at that node. Trajectories actually exist. -/
def SameAllNodeStepJets (o ell : V) (x y : GraphRates G) : Prop :=
  ∀ v : V, ∃ z q : ℝ → V → ℝ,
    IsLocatedGraphSolution v o x (fun _ => 1) z ∧ z 0=0 ∧
    IsLocatedGraphSolution v ell y (fun _ => 1) q ∧ q 0=0 ∧
    stepOutputJet (fun s => z s v)=stepOutputJet (fun s => q s v)

/-- Low-order actual experimental data are EXACTLY the two diagonal moments,
with no hidden eigenvalue observations or assumed positive competitor. -/
theorem all_node_step_jets_iff_moments {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (x : PositiveGraphRateSpace G)
    (y : GraphRates G) :
    SameAllNodeStepJets o ell x.val y ↔
      diagonalTwoJet (graphCompartmentMatrix G ell y)=diagonalTwoJet (graphCompartmentMatrix G o x.val) := by
  constructor
  · intro h
    have hm (v : V) :
        (graphCompartmentMatrix G o x.val v v,
          (graphCompartmentMatrix G o x.val*graphCompartmentMatrix G o x.val) v v) =
        (graphCompartmentMatrix G ell y v v,
          (graphCompartmentMatrix G ell y*graphCompartmentMatrix G ell y) v v) := by
      obtain ⟨z,q,hz,hz0,hq,hq0,he⟩ := h v
      rw [constant_input_collocated_jet v hz hz0,constant_input_collocated_jet v hq hq0] at he
      exact he
    exact Prod.ext (funext (fun v => (congrArg Prod.fst (hm v)).symm))
      (funext (fun v => (congrArg Prod.snd (hm v)).symm))
  · intro h
    have hy : PositiveGraphRates y := by
      rw [graph_diagonalTwoJet_fiber_unique hG p ell x y h]
      exact (relocatePositiveLeak hG o ell x).property
    intro v
    obtain ⟨z,hz,_⟩ := located_forced_ODE_existsUnique hG v o x (fun _ => 1) continuous_const 0 0
    obtain ⟨q,hq,_⟩ := located_forced_ODE_existsUnique hG v ell ⟨y,hy⟩ (fun _ => 1) continuous_const 0 0
    refine ⟨z,q,hz.1,hz.2,hq.1,hq.2,?_⟩
    rw [constant_input_collocated_jet v hz.1 hz.2,constant_input_collocated_jet v hq.1 hq.2]
    exact Prod.ext (congrArg (fun z : (V → ℝ) × (V → ℝ) => z.1 v) h).symm
      (congrArg (fun z : (V → ℝ) × (V → ℝ) => z.2 v) h).symm

abbrev AllNodeStepJetFiber (o : V) (x : GraphRates G) :=
  Σ ell : V, {y : GraphRates G // SameAllNodeStepJets o ell x y}

def allNodeStepJetFiberEquivMoments {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    AllNodeStepJetFiber o x.val ≃ AllNodeJetFiber o x.val where
  toFun z := ⟨z.1,⟨z.2.val,(all_node_step_jets_iff_moments hG p z.1 x z.2.val).mp z.2.property⟩⟩
  invFun z := ⟨z.1,⟨z.2.val,(all_node_step_jets_iff_moments hG p z.1 x z.2.val).mpr z.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual constant-input experiments already leave exactly one real model per
leak site, even if individual reference outputs hide modes or have repeated poles. -/
theorem all_node_actual_step_fiber_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    Nonempty (AllNodeStepJetFiber o x.val ≃ V) ∧
      Finite (AllNodeStepJetFiber o x.val) ∧
      Nat.card (AllNodeStepJetFiber o x.val)=Fintype.card V := by
  let E := (allNodeStepJetFiberEquivMoments hG p x).trans (allNodeJetFiberEquivSites hG p x)
  exact ⟨⟨E⟩,Finite.of_injective E E.injective,(Nat.card_congr E).trans Nat.card_eq_fintype_card⟩

/-- No further collocated continuous experiment can distinguish the models
left by these low-order data. Unique actual trajectories are constructed. -/
theorem all_node_jets_determine_all_collocated_histories {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (x : PositiveGraphRateSpace G)
    (y : GraphRates G) (hy : SameAllNodeStepJets o ell x.val y) :
    ∀ (v : V) (u : ℝ → ℝ), Continuous u →
      ∃ z q : ℝ → V → ℝ,
        IsLocatedGraphSolution v o x.val u z ∧ z 0=0 ∧
        IsLocatedGraphSolution v ell y u q ∧ q 0=0 ∧
        (∀ s : ℝ, z s v=q s v) ∧
        (∀ z',IsLocatedGraphSolution v o x.val u z' → z' 0=0 → z'=z) ∧
        (∀ q',IsLocatedGraphSolution v ell y u q' → q' 0=0 → q'=q) := by
  have hj := (all_node_step_jets_iff_moments hG p ell x y).mp hy
  rw [graph_diagonalTwoJet_fiber_unique hG p ell x y hj]
  exact leak_location_all_input_indistinguishability hG o ell x

end HydrologyTree
