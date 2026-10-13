import HydrologyTree.LeakSlideJacobian
import HydrologyTree.GraphFullTheory
import HydrologyTree.LocatedLeakFiber

/-! Actual Frechet Jacobians of the independently defined coefficient map with
separate observation and leak vertices. All positive-rate singularities are
included in the exact transport; regularity is a later full-response conclusion. -/
open Matrix Polynomial Filter
open scoped Topology
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def locatedGraphCoefficientMap (n : ℕ) (o ell : V) (y : GraphRates G) : PathCoefficients n :=
  (cut (n+1) (graphCompartmentMatrix G ell y).charpoly,
    cut n (diagonalCofactor (graphCompartmentMatrix G ell y) o))

/-- Only a fixed, explicitly given output-coordinate permutation is applied. -/
def normalizedLocatedGraphCoefficients {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) : GraphRates G :=
  graphRateEquiv p (coefficientArrayEquiv n (locatedGraphCoefficientMap n o ell y))

def locatedGraphJacobian {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) : ℝ := endJacobian (normalizedLocatedGraphCoefficients p ell) y

lemma normalizedLocated_at_root {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    normalizedLocatedGraphCoefficients p o=normalizedGraphCoefficients p := rfl

lemma normalizedLocated_relocate {n : ℕ} (hG : G.IsTree) {o : V} (p : RootedTreePresentation n G o)
    (u v : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    normalizedLocatedGraphCoefficients p v (relocateLeakRates hG u v y)=normalizedLocatedGraphCoefficients p u y := by
  have he := relocatePositiveLeak_response hG u v ⟨y,hy⟩
  simp only [normalizedLocatedGraphCoefficients,locatedGraphCoefficientMap,
    relocateLeakRates_eq_positive hG u v y hy]
  rw [he.1,(he.2 o).1]

lemma located_coefficients_neighborhood {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    normalizedLocatedGraphCoefficients p ell =ᶠ[𝓝 y]
      normalizedGraphCoefficients p ∘ relocateLeakRates hG ell o := by
  filter_upwards [positiveGraphRates_eventually y hy] with z hz
  exact (normalizedLocated_relocate hG p ell o z hz).symm

lemma differentiableAt_normalizedGraphCoefficients {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (y : GraphRates G) :
    DifferentiableAt ℝ (normalizedGraphCoefficients p) y := by
  exact (graphRateEquiv p).toContinuousLinearEquiv.differentiableAt.comp y
    ((coefficientArrayEquiv n).toContinuousLinearEquiv.differentiableAt.comp y
      (differentiable_graphCoefficientMap p y))

/-- Differentiability of the actual alternate-leak coefficient map is proved,
not imposed along with the determinant formula. -/
theorem differentiableAt_located_coefficients {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    DifferentiableAt ℝ (normalizedLocatedGraphCoefficients p ell) y := by
  have hR := (relocateLeakRates_differentiable_regular hG ell o y hy).1
  have hF := differentiableAt_normalizedGraphCoefficients p (relocateLeakRates hG ell o y)
  exact ((hF.comp y hR).hasFDerivAt.congr_of_eventuallyEq
    (located_coefficients_neighborhood hG p ell y hy)).differentiableAt

/-- Exact derivative determinant transport holds at EVERY positive vector,
including positive spectral-collision points with zero coefficient Jacobian. -/
theorem locatedGraphJacobian_transport {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    locatedGraphJacobian p ell y=graphCanonicalJacobian p (relocateLeakRates hG ell o y)*
      endJacobian (relocateLeakRates hG ell o) y := by
  have hR := (relocateLeakRates_differentiable_regular hG ell o y hy).1
  have hF := differentiableAt_normalizedGraphCoefficients p (relocateLeakRates hG ell o y)
  have he := located_coefficients_neighborhood hG p ell y hy
  have hJ : endJacobian (normalizedLocatedGraphCoefficients p ell) y=
      endJacobian (normalizedGraphCoefficients p ∘ relocateLeakRates hG ell o) y := by
    rw [endJacobian,endJacobian,he.fderiv_eq]
  exact hJ.trans (endJacobian_comp hF hR)

/-- The scalar multiplier is completely explicit: old leak times new-map
Jacobian equals new leak times root-map Jacobian, with no hidden sign factor. -/
theorem locatedGraphJacobian_leak_weight {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    y.1*locatedGraphJacobian p ell y=(relocateLeakRates hG ell o y).1*
      graphCanonicalJacobian p (relocateLeakRates hG ell o y) := by
  rw [locatedGraphJacobian_transport hG p ell y hy]
  have hR := leakWalkJacobian_leak_weight (Classical.choice (hG.connected ell o)) y hy
  change y.1*endJacobian (relocateLeakRates hG ell o) y=(relocateLeakRates hG ell o y).1 at hR
  calc
    _ = (y.1*endJacobian (relocateLeakRates hG ell o) y)*graphCanonicalJacobian p (relocateLeakRates hG ell o y) := by ring
    _ = _ := by rw [hR]

/-- No positive-rate singularity is introduced or removed by relocating a leak. -/
theorem locatedGraphJacobian_regular_iff {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G) (hy : PositiveGraphRates y) :
    locatedGraphJacobian p ell y ≠ 0 ↔ graphCanonicalJacobian p (relocateLeakRates hG ell o y) ≠ 0 := by
  rw [locatedGraphJacobian_transport hG p ell y hy,mul_ne_zero_iff]
  exact and_iff_left (relocateLeakRates_differentiable_regular hG ell o y hy).2

/-- Every actual positive alternate-leak realization of a full target is regular;
this is a conclusion of the full-response data and proved derivative transport. -/
theorem positive_located_full_response_regular {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : PositiveGraphRateSpace G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0<r i)
    (hw : ∀ i, 0<w i) (hm : (∑ i, w i)=1) (hy : HasLocatedStieltjesResponse o ell y.val r w) :
    locatedGraphJacobian p ell y.val ≠ 0 := by
  apply (locatedGraphJacobian_regular_iff hG p ell y.val y.property).mpr
  rw [relocateLeakRates_eq_positive hG ell o y.val y.property]
  have hR : HasGraphStieltjesResponse o (relocatePositiveLeak hG ell o y).val r w :=
    (located_response_relocate hG o ell o y r w).mp hy
  exact graph_full_response_regular p r w hr hpos hw hm ⟨_,hR⟩

/-- The complete original graph coefficient factorization supplies an exact
formula on the positive alternate-leak domain, using the explicitly constructed
rational relocation. This is NOT yet an all-real polynomial identity at zero boundaries. -/
theorem all_positive_located_jacobian_formula {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ (ell : V) (y : GraphRates G), PositiveGraphRates y →
      y.1*locatedGraphJacobian p ell y=(relocateLeakRates hG ell o y).1 * ε *
        originalTreeRateMonomial p.tree ((graphRateEquiv p).symm (relocateLeakRates hG ell o y)) *
        originalTreeSiblingProduct p.tree ((graphRateEquiv p).symm (relocateLeakRates hG ell o y)) := by
  obtain ⟨ε,hε,hJ⟩ := graph_full_coefficient_jacobian p
  refine ⟨ε,hε,?_⟩
  intro ell y hy
  rw [locatedGraphJacobian_leak_weight hG p ell y hy,hJ]
  ring

end HydrologyTree
