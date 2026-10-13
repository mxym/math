import HydrologyTree.Coefficients

noncomputable section
namespace HydrologyTree
open Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative block occurring in polynomial numerator/denominator gluing. -/
def repeatedBlock (L C : E →L[ℝ] F) : (E × E) →L[ℝ] (F × F) :=
  (L.comp (ContinuousLinearMap.fst ℝ E E)).prod
    (C.comp (ContinuousLinearMap.fst ℝ E E) +
      L.comp (ContinuousLinearMap.snd ℝ E E))

@[simp] theorem repeatedBlock_apply (L C : E →L[ℝ] F) (x : E × E) :
    repeatedBlock L C x = (L x.1, C x.1 + L x.2) := rfl

lemma toMatrix_repeatedBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Basis ι ℝ E) (bF : Basis ι ℝ F) (L C : E →L[ℝ] F) :
    LinearMap.toMatrix (bE.prod bE) (bF.prod bF) (repeatedBlock L C).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bE bF L.toLinearMap) 0
        (LinearMap.toMatrix bE bF C.toLinearMap)
        (LinearMap.toMatrix bE bF L.toLinearMap) := by
  ext i j
  cases i <;> cases j <;> simp [LinearMap.toMatrix_apply, repeatedBlock]

/-- An exact determinant theorem: no nonsingularity assumptions on either block. -/
theorem det_repeatedBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Basis ι ℝ E) (bF : Basis ι ℝ F) (L C : E →L[ℝ] F) :
    (LinearMap.toMatrix (bE.prod bE) (bF.prod bF)
      (repeatedBlock L C).toLinearMap).det =
      (LinearMap.toMatrix bE bF L.toLinearMap).det ^ 2 := by
  rw [toMatrix_repeatedBlock, Matrix.det_fromBlocks_zero₁₂, pow_two]

end HydrologyTree
