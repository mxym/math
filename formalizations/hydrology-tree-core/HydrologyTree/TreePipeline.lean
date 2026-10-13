import HydrologyTree.TreeStepSemantics
import HydrologyTree.CatenaryOrientation
import HydrologyTree.LinearConjugation

/-! Complete physical parent pipeline in independent child coordinates. Only
smaller-child differentiability appears in the local induction lemmas; the
following tree induction must discharge it, not assume the main conclusion. -/
open Polynomial Module
noncomputable section
set_option maxHeartbeats 600000
namespace HydrologyTree


/-- Apply the actual normalized physical coefficient map independently in each child. -/
def treeChildStep {n : ℕ} (t : OrderedTree n) : TreeWork t → TreeWork t :=
  keepFunction (F := ℝ × (RootChild t → ℝ))
    (dependentPiEnd (fun c => normalizedPhysicalTree (childTree t c)))

/-- The proved all-arity local step, conjugated into independent child coordinates. -/
def treeLocalStep {n : ℕ} (t : OrderedTree n) (z : TreeWork t) : TreeWork t :=
  (prepareFamilyEquiv (childEdgeCount t)).symm
    (normalizedBranchStep (TreeBranchDegrees t) (prepareFamilyEquiv (childEdgeCount t) z))

def treePipeline {n : ℕ} (t : OrderedTree n) : TreeWork t → TreeWork t :=
  treeLocalStep t ∘ (treeChildStep t ∘ rootCoupling (childLeakMap t))

lemma treeChildStep_actual {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    prepareFamilyEquiv (childEdgeCount t)
      (treeChildStep t (rootCoupling (childLeakMap t) (originalWorkEquiv t x))) =
        actualBranchInputs t x := by
  rw [originalWorkEquiv_originalCoupling,rootCoupling_physical_coordinates]
  rfl

/-- Exact end-to-end physical identification, with all rates and degenerate
boundaries included and no coefficient-Jacobian assumption. -/
theorem treePipeline_actual {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treePipeline t (originalWorkEquiv t x) =
      parentCoefficientWorkEquiv t (physicalCoefficientMap t x) := by
  change (prepareFamilyEquiv (childEdgeCount t)).symm
    (normalizedBranchStep (TreeBranchDegrees t)
      (prepareFamilyEquiv (childEdgeCount t)
        (treeChildStep t (rootCoupling (childLeakMap t) (originalWorkEquiv t x))))) = _
  rw [treeChildStep_actual,actualBranchInputs_normalized]

lemma differentiable_treeLocalStep {n : ℕ} (t : OrderedTree n) : Differentiable ℝ (treeLocalStep t) := by
  unfold treeLocalStep
  apply differentiable_linear_conjugate (prepareFamilyEquiv (childEdgeCount t))
  exact differentiable_normalizedBranchStep (TreeBranchDegrees t)

lemma differentiableAt_treeChildStep {n : ℕ} (t : OrderedTree n) (z : TreeWork t)
    (hc : ∀ c : RootChild t, DifferentiableAt ℝ (normalizedPhysicalTree (childTree t c)) (z.1 c)) :
    DifferentiableAt ℝ (treeChildStep t) z :=
  (hasFDerivAt_keepFunction z (hasFDerivAt_dependentPiEnd _ _ hc).differentiableAt).differentiableAt

lemma treeChildStep_jacobian {n : ℕ} (t : OrderedTree n) (z : TreeWork t)
    (hc : ∀ c : RootChild t, DifferentiableAt ℝ (physicalCoefficientMap (childTree t c)) (z.1 c)) :
    endJacobian (treeChildStep t) z =
      ∏ c : RootChild t, treeCanonicalJacobian (childTree t c) (z.1 c) := by
  have hn (c : RootChild t) : DifferentiableAt ℝ (normalizedPhysicalTree (childTree t c)) (z.1 c) :=
    (coefficientArrayEquiv (childEdgeCount t c)).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp _ (hc c)
  rw [treeChildStep,endJacobian_keepFunction _ _
    (hasFDerivAt_dependentPiEnd _ _ hn).differentiableAt,endJacobian_dependentPiEnd _ _ hn]
  exact Finset.prod_congr rfl (fun c _ => normalizedPhysicalTree_jacobian _ _ (hc c))

lemma rootCoupling_endJacobian {n : ℕ} (t : OrderedTree n) (z : TreeWork t) :
    endJacobian (rootCoupling (childLeakMap t)) z = ∏ c : RootChild t, (z.1 c).1 0 := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_rootCoupling (childLeakMap t) z),
    ← LinearMap.det_toMatrix ((Module.finBasis ℝ (ChildStates t)).prod
      ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ (RootChild t)))),det_rootCouplingDerivative]
  rfl

/-- Sibling resultant product in a fixed enumeration of the actual child polynomials. -/
def treeSiblingResultant {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  pairwiseResultants (List.ofFn (fun i : Fin (Fintype.card (RootChild t)) =>
    childCharacteristic t x ((Fintype.equivFin (RootChild t)).symm i)))

lemma actualBranchInputs_resultants {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    pairwiseResultants (familyPolynomials (ChildFactorDegrees (TreeBranchDegrees t))
      (actualBranchInputs t x).1.1) = treeSiblingResultant t x := by
  rw [actualBranchInputs_denominators,piScaled_polynomials]
  congr 1
  congr 1
  funext i
  exact physicalCoefficientMap_first_reconstruct _ _

lemma actualBranchInputs_weight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    scaleFamilyWeight (TreeBranchDegrees t) (actualBranchInputs t x).1.2 =
      ∏ c : RootChild t, (x.1 c.val*outwardByVertex x.2 c.val) ^ childEdgeCount t c := by
  exact prepareFamilyEquiv_scaleWeight _ _

/-- The exact local parent Jacobian on actual child outputs and physical connector products. -/
lemma treeLocalStep_actual_jacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    endJacobian (treeLocalStep t)
      (treeChildStep t (rootCoupling (childLeakMap t) (originalWorkEquiv t x))) =
      (-1 : ℝ)^n * treeSiblingResultant t x ^ 2 *
        ∏ c : RootChild t, (x.1 c.val*outwardByVertex x.2 c.val) ^ childEdgeCount t c := by
  unfold treeLocalStep
  rw [endJacobian_linear_conjugate (prepareFamilyEquiv (childEdgeCount t))
    (normalizedBranchStep (TreeBranchDegrees t)) _
    (differentiable_normalizedBranchStep (TreeBranchDegrees t) _)]
  rw [treeChildStep_actual,normalizedBranchStep_jacobian,treeBranchDegree_sum,
    actualBranchInputs_resultants,actualBranchInputs_weight]

end HydrologyTree
