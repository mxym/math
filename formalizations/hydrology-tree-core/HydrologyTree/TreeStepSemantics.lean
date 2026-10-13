import HydrologyTree.TreePreparation
import HydrologyTree.PhysicalBranchRecovery

/-! End-to-end identification of the composed local all-child coefficient step
with the original physical tree's actual characteristic and root cofactor. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

lemma scaleLeading_of_leading (n : ℕ) (a : ℝ) (F : Coeff n) :
    scaleLeading n (leadingEquiv n (a,F)) = a • monicPoly F := by
  rw [scaleLeading,LinearEquiv.symm_apply_apply]
  exact (congrFun (scaleMonic_eq_comp (n := n)) (a,F)).symm

lemma scaledPhysicalChildSlot {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    (scaleLeading (childEdgeCount t c) (leadingEquiv (childEdgeCount t c)
      (x.1 c.val*outwardByVertex x.2 c.val,
        (physicalCoefficientMap (childTree t c) (childRates t c x)).2)) : ℝ[X]) =
      physicalChildNumerator t x c := by
  rw [scaleLeading_of_leading]
  change (x.1 c.val*outwardByVertex x.2 c.val) •
    (monicPoly (physicalCoefficientMap (childTree t c) (childRates t c x)).2 : ℝ[X]) = _
  rw [physicalCoefficientMap_second_reconstruct,Polynomial.smul_eq_C_mul]
  rfl

lemma actualBranchInputs_numerator {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    familyNumerator (ChildFactorDegrees (TreeBranchDegrees t)) (actualBranchInputs t x).1.1
      (scaleFamily (TreeBranchDegrees t) (actualBranchInputs t x).1.2) =
        branchNumeratorSum (childCharacteristic t x) (physicalChildNumerator t x) := by
  rw [actualBranchInputs_denominators,actualBranchInputs_numeratorSlots,piScaled_scale,serializedNumerator]
  have hP : (fun c : RootChild t =>
      (monicPoly (physicalCoefficientMap (childTree t c) (childRates t c x)).1 : ℝ[X])) =
      childCharacteristic t x := by
    funext c
    exact physicalCoefficientMap_first_reconstruct _ _
  rw [hP]
  congr 1
  funext c
  exact scaledPhysicalChildSlot t x c

lemma actualBranchInputs_characteristic {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    branchStepPolynomial (TreeBranchDegrees t) (actualBranchInputs t x) = physicalCharacteristic t x := by
  rw [branchStepPolynomial,actualBranchInputs_product,actualBranchInputs_numerator,
    physical_branch_numerator_sum,physicalRootCofactor_child_product]
  change (X+C ((rateChart t x).1 0)) * _ - ((X+C ((rateChart t x).1 0))*_ - _) = _
  ring

lemma actualBranchInputs_cofactor {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    familyProduct (ChildFactorDegrees (TreeBranchDegrees t)) (actualBranchInputs t x).1.1 =
      cut (ChildFactorDegrees (TreeBranchDegrees t)).sum (physicalRootCofactor t x) := by
  have h := congrArg (cut (ChildFactorDegrees (TreeBranchDegrees t)).sum) (actualBranchInputs_product t x)
  rw [coe_monicPoly,map_add,cut_X_pow_of_le _ _ le_rfl,zero_add,cut_coe] at h
  exact h

/-- Exact coefficient identity, with all physical diagonals and scale factors.
This is not an assumption about what the independent child maps represent. -/
theorem actualBranchInputs_coefficients {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    branchStepCoefficients (TreeBranchDegrees t) (actualBranchInputs t x) =
      pathCoefficientsCast (treeBranchDegree_sum t).symm (physicalCoefficientMap t x) := by
  rw [branchStepCoefficients,actualBranchInputs_characteristic,actualBranchInputs_cofactor]
  exact (pathCoefficientsCast_cut (treeBranchDegree_sum t).symm _ _).symm

/-- The local normal-form map produces exactly the original physical coefficient
output followed by the specified fixed linear return map. -/
theorem actualBranchInputs_normalized {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (prepareFamilyEquiv (childEdgeCount t)).symm
      (normalizedBranchStep (TreeBranchDegrees t) (actualBranchInputs t x)) =
        parentCoefficientWorkEquiv t (physicalCoefficientMap t x) := by
  rw [normalizedBranchStep_actual,actualBranchInputs_coefficients]
  rfl

end HydrologyTree
