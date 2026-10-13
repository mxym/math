import HydrologyTree.GraphMatrixTransport
import HydrologyTree.SubtreeProducts

/-! Actual graph characteristic/cofactor coefficients and their Frechet
Jacobian. The output coordinate permutation is explicit; no determinant
identity is imposed as a definition or hypothesis. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def graphCoefficientMap (n : ℕ) (o : V) (y : GraphRates G) : PathCoefficients n :=
  (cut (n+1) (graphCharacteristic o y),cut n (graphRootCofactor o y))

lemma graphCoefficientMap_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) : graphCoefficientMap n o (graphRateEquiv p x)=physicalCoefficientMap p.tree x := by
  simp only [graphCoefficientMap,graphCharacteristic_transport,graphRootCofactor_transport,
    physicalCoefficientMap]

lemma graphCoefficientMap_eq_comp {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    graphCoefficientMap n o = fun y => physicalCoefficientMap p.tree ((graphRateEquiv p).symm y) := by
  funext y
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [graphCoefficientMap_transport,LinearEquiv.symm_apply_apply]

theorem differentiable_graphCoefficientMap {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    Differentiable ℝ (graphCoefficientMap (G := G) n o) := by
  rw [graphCoefficientMap_eq_comp p]
  intro y
  exact (differentiable_physicalCoefficientMap p.tree ((graphRateEquiv p).symm y)).comp y
    (graphRateEquiv p).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt

/-- Ascending actual polynomial coefficients, relabelled by the same proved
coordinate permutation as the actual graph rate vector. -/
def normalizedGraphCoefficients {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) : GraphRates G :=
  graphRateEquiv p (coefficientArrayEquiv n (graphCoefficientMap n o y))

lemma normalizedGraphCoefficients_conjugate {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    normalizedGraphCoefficients p = fun y =>
      graphRateEquiv p (normalizedPhysicalTree p.tree ((graphRateEquiv p).symm y)) := by
  funext y
  simp only [normalizedGraphCoefficients,graphCoefficientMap_eq_comp p,normalizedPhysicalTree]

/-- Determinant of the actual Frechet derivative after explicit coordinate permutation. -/
def graphCanonicalJacobian {n : ℕ} {o : V} (p : RootedTreePresentation n G o) (y : GraphRates G) : ℝ :=
  endJacobian (normalizedGraphCoefficients p) y

theorem graphCanonicalJacobian_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) :
    graphCanonicalJacobian p y=treeCanonicalJacobian p.tree ((graphRateEquiv p).symm y) := by
  have hf : DifferentiableAt ℝ (normalizedPhysicalTree p.tree) ((graphRateEquiv p).symm y) :=
    (coefficientArrayEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp _
      (differentiable_physicalCoefficientMap p.tree _)
  rw [graphCanonicalJacobian,normalizedGraphCoefficients_conjugate]
  exact (endJacobian_conjugate (graphRateEquiv p).toContinuousLinearEquiv _ _ hf).trans
    (normalizedPhysicalTree_jacobian p.tree _ (differentiable_physicalCoefficientMap p.tree _))

/-- All real graph rates, including zero and negative rates, satisfy the exact
factorization after the proved rate/vertex transport, with one fixed sign. -/
theorem graph_full_coefficient_jacobian {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ y : GraphRates G,
      graphCanonicalJacobian p y=ε * originalTreeRateMonomial p.tree ((graphRateEquiv p).symm y) *
        originalTreeSiblingProduct p.tree ((graphRateEquiv p).symm y) := by
  obtain ⟨ε,hε,hformula⟩ := full_tree_standard_jacobian p.tree
  exact ⟨ε,hε,fun y => (graphCanonicalJacobian_transport p y).trans (hformula _)⟩

/-- The independent graph hypotheses themselves supply the presentation needed
by the exact actual-coefficient Jacobian theorem. -/
theorem finite_graph_coefficient_jacobian {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1) :
    ∃ p : RootedTreePresentation n G o,
      Differentiable ℝ (graphCoefficientMap (G := G) n o) ∧
      ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ y : GraphRates G,
        graphCanonicalJacobian p y=ε * originalTreeRateMonomial p.tree ((graphRateEquiv p).symm y) *
          originalTreeSiblingProduct p.tree ((graphRateEquiv p).symm y) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  exact ⟨p,differentiable_graphCoefficientMap p,graph_full_coefficient_jacobian p⟩

end HydrologyTree
