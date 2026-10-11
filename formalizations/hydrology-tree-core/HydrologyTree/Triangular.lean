import HydrologyTree.BlockJacobian

/-! Actual triangular linear maps, with fully specified coefficient bases. -/
open Module
noncomputable section
namespace HydrologyTree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def lowerBlock (L : E →L[ℝ] E) (C : E →L[ℝ] F) (M : F →L[ℝ] F) :
    (E × F) →L[ℝ] (E × F) :=
  (L.comp (ContinuousLinearMap.fst ℝ E F)).prod
    (C.comp (ContinuousLinearMap.fst ℝ E F) + M.comp (ContinuousLinearMap.snd ℝ E F))

@[simp] lemma lowerBlock_apply (L : E →L[ℝ] E) (C : E →L[ℝ] F)
    (M : F →L[ℝ] F) (x : E × F) :
    lowerBlock L C M x = (L x.1, C x.1 + M x.2) := rfl

lemma toMatrix_lowerBlock {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (bE : Basis ι ℝ E) (bF : Basis κ ℝ F)
    (L : E →L[ℝ] E) (C : E →L[ℝ] F) (M : F →L[ℝ] F) :
    LinearMap.toMatrix (bE.prod bF) (bE.prod bF) (lowerBlock L C M).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bE bE L.toLinearMap) 0
        (LinearMap.toMatrix bE bF C.toLinearMap) (LinearMap.toMatrix bF bF M.toLinearMap) := by
  ext i j
  cases i <;> cases j <;> simp [LinearMap.toMatrix_apply, lowerBlock]

theorem det_lowerBlock {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (bE : Basis ι ℝ E) (bF : Basis κ ℝ F)
    (L : E →L[ℝ] E) (C : E →L[ℝ] F) (M : F →L[ℝ] F) :
    (LinearMap.toMatrix (bE.prod bF) (bE.prod bF) (lowerBlock L C M).toLinearMap).det =
      (LinearMap.toMatrix bE bE L.toLinearMap).det *
        (LinearMap.toMatrix bF bF M.toLinearMap).det := by
  rw [toMatrix_lowerBlock, Matrix.det_fromBlocks_zero₁₂]

end HydrologyTree
