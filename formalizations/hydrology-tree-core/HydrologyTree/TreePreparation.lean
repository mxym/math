import HydrologyTree.OriginalWorkCoordinates
import HydrologyTree.SerializedNumerator
import HydrologyTree.DependentJacobian
import HydrologyTree.PhysicalRecursion
import HydrologyTree.CatenaryOrientation

/-! Rate-independent preparation and coefficient return for the ACTUAL physical
branching tree. Sizes, coefficient identities and coordinate normalization are proved. -/
open Polynomial Module Matrix
noncomputable section
namespace HydrologyTree

abbrev TreeBranchDegrees {n : ℕ} (t : OrderedTree n) := degreeSequence (childEdgeCount t)
abbrev TreeWork {n : ℕ} (t : OrderedTree n) := IndependentChildData (childEdgeCount t)

lemma treeBranchDegree_sum {n : ℕ} (t : OrderedTree n) :
    (ChildFactorDegrees (TreeBranchDegrees t)).sum = n := by
  rw [← degreeSequence_addOne,degreeSequence_sum,sum_child_vertices]

def pathCoefficientsCast {n m : ℕ} (h : n=m) : PathCoefficients n ≃ₗ[ℝ] PathCoefficients m := by
  subst m
  exact LinearEquiv.refl ℝ _

lemma pathCoefficientsCast_cut {n m : ℕ} (h : n=m) (P F : ℝ[X]) :
    pathCoefficientsCast h (cut (n+1) P,cut n F) = (cut (m+1) P,cut m F) := by
  subst m
  rfl

lemma pathCoefficientsCast_dot {n m : ℕ} (h : n=m) (p q : PathCoefficients n) :
    pathCoefficientDot m (pathCoefficientsCast h p) (pathCoefficientsCast h q) =
      pathCoefficientDot n p q := by
  subst m
  rfl

/-- The actual parent coefficient output, in the same independent-child coordinates
as the input. All constituent transformations are fixed linear equivalences. -/
def parentCoefficientWorkEquiv {n : ℕ} (t : OrderedTree n) : PathCoefficients n ≃ₗ[ℝ] TreeWork t :=
  ((pathCoefficientsCast (treeBranchDegree_sum t).symm).trans
    (branchCoefficientEquiv (TreeBranchDegrees t))).trans (prepareFamilyEquiv (childEdgeCount t)).symm

lemma parentCoefficientWorkEquiv_dot {n : ℕ} (t : OrderedTree n) (p q : PathCoefficients n) :
    independentChildDot (childEdgeCount t) (parentCoefficientWorkEquiv t p) (parentCoefficientWorkEquiv t q) =
      pathCoefficientDot n p q := by
  rw [← prepareFamilyEquiv_dot]
  have hp : prepareFamilyEquiv (childEdgeCount t) (parentCoefficientWorkEquiv t p) =
      branchCoefficientEquiv (TreeBranchDegrees t) (pathCoefficientsCast (treeBranchDegree_sum t).symm p) := by
    exact (prepareFamilyEquiv (childEdgeCount t)).apply_symm_apply _
  have hq : prepareFamilyEquiv (childEdgeCount t) (parentCoefficientWorkEquiv t q) =
      branchCoefficientEquiv (TreeBranchDegrees t) (pathCoefficientsCast (treeBranchDegree_sum t).symm q) := by
    exact (prepareFamilyEquiv (childEdgeCount t)).apply_symm_apply _
  rw [hp,hq]
  change _ = pathCoefficientDot n p q
  rw [branchInputDot,branchCoefficientEquiv_dot,pathCoefficientsCast_dot]

/-- Return the parent coefficient array to the original physical coordinate array. -/
def treeCoordinateReturn {n : ℕ} (t : OrderedTree n) : PathCoefficients n ≃ₗ[ℝ] TreeRates n :=
  (parentCoefficientWorkEquiv t).trans (originalWorkEquiv t).symm

lemma treeCoordinateReturn_dot {n : ℕ} (t : OrderedTree n) (p q : PathCoefficients n) :
    physicalRateDot n (treeCoordinateReturn t p) (treeCoordinateReturn t q) = pathCoefficientDot n p q := by
  rw [← originalWorkEquiv_dot t]
  have hp : originalWorkEquiv t (treeCoordinateReturn t p) = parentCoefficientWorkEquiv t p :=
    (originalWorkEquiv t).apply_symm_apply _
  have hq : originalWorkEquiv t (treeCoordinateReturn t q) = parentCoefficientWorkEquiv t q :=
    (originalWorkEquiv t).apply_symm_apply _
  rw [hp,hq,parentCoefficientWorkEquiv_dot]

def treeCoordinateDet {n : ℕ} (t : OrderedTree n) : ℝ :=
  (LinearMap.toMatrix (catenaryArrayOutputBasis n) (catenaryArrayInputBasis n)
    (treeCoordinateReturn t).toLinearMap).det

/-- The global coordinate normalization has magnitude one, independently of rates. -/
theorem treeCoordinateDet_sq {n : ℕ} (t : OrderedTree n) : treeCoordinateDet t ^ 2 = 1 := by
  apply det_sq_of_basisDot_preserved (catenaryArrayOutputBasis n) (catenaryArrayInputBasis n)
  intro p q
  rw [arrayInput_basisDot,arrayOutput_basisDot]
  exact treeCoordinateReturn_dot t p q

/-- Child coefficient outputs and the actual root/edge-product data at an original rate vector. -/
def actualBranchInputs {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : BranchStepInputs (TreeBranchDegrees t) :=
  prepareFamilyEquiv (childEdgeCount t)
    ((fun c => normalizedPhysicalTree (childTree t c) (childRates t c x)),
      ((rateChart t x).1 0,fun c => x.1 c.val*outwardByVertex x.2 c.val))

lemma actualBranchInputs_denominators {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (actualBranchInputs t x).1.1 =
      piScaledEquiv (childEdgeCount t) (fun c => (physicalCoefficientMap (childTree t c) (childRates t c x)).1) := by
  have h := prepareFamilyEquiv_apply (childEdgeCount t)
    ((fun c => normalizedPhysicalTree (childTree t c) (childRates t c x)),
      ((rateChart t x).1 0,fun c => x.1 c.val*outwardByVertex x.2 c.val))
  simpa only [actualBranchInputs,normalizedPhysicalTree,LinearEquiv.symm_apply_apply] using
    congrArg (fun z : BranchStepInputs (TreeBranchDegrees t) => z.1.1) h

lemma actualBranchInputs_numeratorSlots {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (actualBranchInputs t x).1.2 =
      piScaledEquiv (childEdgeCount t) (fun c => leadingEquiv (childEdgeCount t c)
        (x.1 c.val*outwardByVertex x.2 c.val,
          (physicalCoefficientMap (childTree t c) (childRates t c x)).2)) := by
  have h := prepareFamilyEquiv_apply (childEdgeCount t)
    ((fun c => normalizedPhysicalTree (childTree t c) (childRates t c x)),
      ((rateChart t x).1 0,fun c => x.1 c.val*outwardByVertex x.2 c.val))
  simpa only [actualBranchInputs,normalizedPhysicalTree,LinearEquiv.symm_apply_apply] using
    congrArg (fun z : BranchStepInputs (TreeBranchDegrees t) => z.1.2) h

lemma actualBranchInputs_product {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (monicPoly (familyProduct (ChildFactorDegrees (TreeBranchDegrees t)) (actualBranchInputs t x).1.1) : ℝ[X]) =
      physicalRootCofactor t x := by
  rw [actualBranchInputs_denominators,piScaled_product,physicalRootCofactor_child_product]
  exact Finset.prod_congr rfl (fun c _ => physicalCoefficientMap_first_reconstruct _ _)

end HydrologyTree
