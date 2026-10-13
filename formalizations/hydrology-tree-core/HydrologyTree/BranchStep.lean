import HydrologyTree.FamilyNormalization

/-! Complete all-child local coefficient-Jacobian assembly: actual monic
numerator scaling, actual gluing and actual root polynomial update are composed
with their Frechet derivatives. The global physical-tree induction is separate. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev BranchStepInputs (ms : List ℕ) := FamilyRootInputs (ChildFactorDegrees ms)

def branchScaleStep (ms : List ℕ) : BranchStepInputs ms → BranchStepInputs ms :=
  keepFunction (F := ℝ) (productEndMap id (scaleFamily ms))

def branchGlueStep (ms : List ℕ) : BranchStepInputs ms → BranchStepInputs ms :=
  keepFunction (F := ℝ) (normalizedFamilyGlue (ChildFactorDegrees ms))

def normalizedBranchStep (ms : List ℕ) : BranchStepInputs ms → BranchStepInputs ms :=
  normalizedFamilyRoot (ChildFactorDegrees ms) ∘ (branchGlueStep ms ∘ branchScaleStep ms)

lemma differentiable_branchScaleStep (ms : List ℕ) : Differentiable ℝ (branchScaleStep ms) := by
  intro z
  exact (hasFDerivAt_keepFunction z
    (hasFDerivAt_productEndMap id (scaleFamily ms) z.1 differentiableAt_id
      (differentiable_scaleFamily ms z.1.2)).differentiableAt).differentiableAt

lemma differentiable_branchGlueStep (ms : List ℕ) : Differentiable ℝ (branchGlueStep ms) := by
  intro z
  exact (hasFDerivAt_keepFunction z (differentiable_normalizedFamilyGlue _ z.1)).differentiableAt

lemma differentiable_normalizedBranchStep (ms : List ℕ) : Differentiable ℝ (normalizedBranchStep ms) :=
  (differentiable_normalizedFamilyRoot _).comp
    ((differentiable_branchGlueStep ms).comp (differentiable_branchScaleStep ms))

lemma branchScaleStep_jacobian (ms : List ℕ) (z : BranchStepInputs ms) :
    endJacobian (branchScaleStep ms) z = scaleFamilyWeight ms z.1.2 := by
  rw [branchScaleStep, endJacobian_keepFunction _ _
    (hasFDerivAt_productEndMap id (scaleFamily ms) z.1 differentiableAt_id
      (differentiable_scaleFamily ms z.1.2)).differentiableAt,
    endJacobian_productEndMap _ _ _ differentiableAt_id
      (differentiable_scaleFamily ms z.1.2), endJacobian_scaleFamily]
  simp [endJacobian]

lemma branchGlueStep_jacobian (ms : List ℕ) (z : BranchStepInputs ms) :
    endJacobian (branchGlueStep ms) z =
      pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 := by
  rw [branchGlueStep, endJacobian_keepFunction _ _
    (differentiable_normalizedFamilyGlue _ z.1), normalizedFamilyGlue_jacobian]

/-- All local Jacobian factors are composed, rather than merely proved in isolation.
No nonzero scale, simple root, positive rate, or nonempty-child assumption. -/
theorem normalizedBranchStep_jacobian (ms : List ℕ) (z : BranchStepInputs ms) :
    endJacobian (normalizedBranchStep ms) z =
      (-1 : ℝ)^(ChildFactorDegrees ms).sum *
        pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 *
          scaleFamilyWeight ms z.1.2 := by
  rw [normalizedBranchStep,
    endJacobian_comp (differentiable_normalizedFamilyRoot _ _)
      ((differentiable_branchGlueStep ms _).comp z (differentiable_branchScaleStep ms z)),
    endJacobian_comp (differentiable_branchGlueStep ms _) (differentiable_branchScaleStep ms z),
    normalizedFamilyRoot_jacobian, branchGlueStep_jacobian, branchScaleStep_jacobian]
  change (-1 : ℝ)^(ChildFactorDegrees ms).sum *
    (pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 *
      scaleFamilyWeight ms z.1.2) = _
  ring

def branchStepPolynomial (ms : List ℕ) (z : BranchStepInputs ms) : ℝ[X] :=
  (X+C z.2) * (monicPoly (familyProduct (ChildFactorDegrees ms) z.1.1) : ℝ[X]) -
    familyNumerator (ChildFactorDegrees ms) z.1.1 (scaleFamily ms z.1.2)

/-- Actual parent characteristic/cofactor coefficient output at a root. -/
def branchStepCoefficients (ms : List ℕ) (z : BranchStepInputs ms) :
    Coeff ((ChildFactorDegrees ms).sum+1) × Coeff (ChildFactorDegrees ms).sum :=
  (cut ((ChildFactorDegrees ms).sum+1) (branchStepPolynomial ms z),
    familyProduct (ChildFactorDegrees ms) z.1.1)

def branchCoefficientEquiv (ms : List ℕ) :
    (Coeff ((ChildFactorDegrees ms).sum+1) × Coeff (ChildFactorDegrees ms).sum) ≃ₗ[ℝ]
      BranchStepInputs ms :=
  (rootOutputEquiv (ChildFactorDegrees ms).sum).trans (familyRootEquiv (ChildFactorDegrees ms)).symm

lemma familyRootEquiv_glued (ns : List ℕ) (x : FamilyPairs ns) (d : ℝ) :
    familyRootEquiv ns (normalizedFamilyGlue ns x,d) =
      ((familyGlue ns x).1,(d,(familyGlue ns x).2)) := by
  change rootRegroupEquiv ns.sum
    (familyPairEquiv ns ((familyPairEquiv ns).symm (familyGlue ns x)),d) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma branchStepPolynomial_root (ms : List ℕ) (z : BranchStepInputs ms) :
    branchStepPolynomial ms z =
      rootPolynomial ((familyGlue (ChildFactorDegrees ms) (z.1.1,scaleFamily ms z.1.2)).1,
        (z.2,(familyGlue (ChildFactorDegrees ms) (z.1.1,scaleFamily ms z.1.2)).2)) := by
  unfold branchStepPolynomial rootPolynomial
  rw [familyGlue_numerator_exact]
  rfl

/-- The composed normal-form transformation is exactly the actual coefficient map,
followed by the specified unscaled coefficient permutation. -/
theorem normalizedBranchStep_actual (ms : List ℕ) (z : BranchStepInputs ms) :
    normalizedBranchStep ms z = branchCoefficientEquiv ms (branchStepCoefficients ms z) := by
  change (familyRootEquiv (ChildFactorDegrees ms)).symm
    (rootCoefficientMap (familyRootEquiv (ChildFactorDegrees ms)
      (normalizedFamilyGlue (ChildFactorDegrees ms) (z.1.1,scaleFamily ms z.1.2),z.2))) = _
  rw [familyRootEquiv_glued]
  apply (familyRootEquiv (ChildFactorDegrees ms)).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [branchCoefficientEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change rootCoefficientMap _ = rootOutputEquiv _ (branchStepCoefficients ms z)
  rw [branchStepCoefficients, branchStepPolynomial_root]
  exact (rootOutputEquiv_actual _ _).symm

/-- End-to-end all-arity local coefficient Jacobian with its actual objects. -/
theorem branchStep_actual_jacobian (ms : List ℕ) (z : BranchStepInputs ms) :
    endJacobian (fun w => branchCoefficientEquiv ms (branchStepCoefficients ms w)) z =
      (-1 : ℝ)^(ChildFactorDegrees ms).sum *
        pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 *
          scaleFamilyWeight ms z.1.2 := by
  have he : (fun w => branchCoefficientEquiv ms (branchStepCoefficients ms w)) = normalizedBranchStep ms := by
    funext w
    exact (normalizedBranchStep_actual ms w).symm
  rw [he, normalizedBranchStep_jacobian]

end HydrologyTree
