import HydrologyTree.GraphDiagonalJets
import HydrologyTree.GraphModelInjectivity
import Mathlib.SetTheory.Cardinal.Finite

/-! Exhaustive all-real classification of low-order all-node observation data.
The only remaining freedom is the actual leakage vertex; no full-mode target
is required and no positivity condition is placed on competing parameters. -/
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev AllNodeJetFiber (o : V) (x : GraphRates G) :=
  Σ ell : V, {y : GraphRates G // diagonalTwoJet (graphCompartmentMatrix G ell y)=
    diagonalTwoJet (graphCompartmentMatrix G o x)}

def relocatedJetPoint (hG : G.IsTree) (o : V) (x : PositiveGraphRateSpace G)
    (ell : V) : AllNodeJetFiber o x.val :=
  ⟨ell,⟨(relocatePositiveLeak hG o ell x).val,relocated_diagonalTwoJet hG o ell x⟩⟩

/-- Every real competitor is uniquely the actual relocated model at its own
leak site, rather than an assumed finite list of physically admissible fits. -/
theorem relocatedJetPoint_bijective {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    Function.Bijective (relocatedJetPoint hG o x) := by
  constructor
  · intro u v huv
    exact congrArg Sigma.fst huv
  · rintro ⟨ell,y⟩
    have he := graph_diagonalTwoJet_fiber_unique hG p ell x y.val y.property
    refine ⟨ell,?_⟩
    exact Sigma.subtype_ext (x₀ := relocatedJetPoint hG o x ell) (x₁ := ⟨ell,y⟩) rfl he.symm

/-- Explicit finite classification by the original vertices, independent of
all observable-mode multiplicities and all accidental spectral coincidences. -/
def allNodeJetFiberEquivSites {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    AllNodeJetFiber o x.val ≃ V :=
  (Equiv.ofBijective (relocatedJetPoint hG o x) (relocatedJetPoint_bijective hG p x)).symm

/-- At a known site there is exactly one real model; if the site is unknown
there are exactly |V| real models. Their rate signs are conclusions. -/
theorem all_node_two_jet_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    Finite (AllNodeJetFiber o x.val) ∧ Nat.card (AllNodeJetFiber o x.val)=Fintype.card V ∧
      ∀ z : AllNodeJetFiber o x.val, PositiveGraphRates z.2.val := by
  let E := allNodeJetFiberEquivSites hG p x
  refine ⟨Finite.of_injective E E.injective,?_,?_⟩
  · exact (Nat.card_congr E).trans (Nat.card_eq_fintype_card)
  · rintro ⟨ell,y⟩
    rw [graph_diagonalTwoJet_fiber_unique hG p ell x y.val y.property]
    exact (relocatePositiveLeak hG o ell x).property

/-- These |V| points correspond to distinct actual matrices, not redundant
site labels for identical dynamics. -/
theorem allNodeJetFiber_matrix_injective {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (x : PositiveGraphRateSpace G) :
    Function.Injective (fun z : AllNodeJetFiber o x.val => graphCompartmentMatrix G z.1 z.2.val) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ h
  have hu := (all_node_two_jet_exact_card hG p x).2.2 ⟨a,u⟩
  have hab := equal_graph_matrices_identify_leak_site a b u.val v.val (ne_of_gt hu.1) h
  subst b
  have huv := graphRates_from_matrix_injective a h
  have he : u=v := Subtype.ext huv
  subst v
  rfl

/-- Independent finite graph formulation, with a constructed presentation.
No full-Stieltjes target, simple eigenvalues or positive competing rates occur. -/
theorem finite_tree_all_node_jet_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V)
    (hN : Fintype.card V=n+1) (x : PositiveGraphRateSpace G) :
    Nonempty (AllNodeJetFiber o x.val ≃ V) ∧ Finite (AllNodeJetFiber o x.val) ∧
      Nat.card (AllNodeJetFiber o x.val)=n+1 ∧
      ∀ z : AllNodeJetFiber o x.val, PositiveGraphRates z.2.val := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  obtain ⟨hf,hc,hp⟩ := all_node_two_jet_exact_card hG p x
  exact ⟨⟨allNodeJetFiberEquivSites hG p x⟩,hf,hc.trans hN,hp⟩

end HydrologyTree
