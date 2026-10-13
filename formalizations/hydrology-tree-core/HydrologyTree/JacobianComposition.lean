import HydrologyTree.ProductDerivative

/-! Basis-aware determinant composition for growing coefficient families. -/
open Matrix Module
noncomputable section
namespace HydrologyTree

section Linear
variable {E₀ E F : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def keepLeft (L : E →L[ℝ] F) : (E₀ × E) →L[ℝ] (E₀ × F) :=
  (ContinuousLinearMap.fst ℝ E₀ E).prod (L.comp (ContinuousLinearMap.snd ℝ E₀ E))

@[simp] lemma keepLeft_apply (L : E →L[ℝ] F) (x : E₀ × E) :
    keepLeft L x = (x.1, L x.2) := rfl

lemma toMatrix_keepLeft {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b₀ : Basis ι ℝ E₀) (bE : Basis κ ℝ E)
    (bF : Basis κ ℝ F) (L : E →L[ℝ] F) :
    LinearMap.toMatrix (b₀.prod bE) (b₀.prod bF) (keepLeft L).toLinearMap =
      Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 0 (LinearMap.toMatrix bE bF L.toLinearMap) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, keepLeft, Matrix.one_apply, Finsupp.single_apply, eq_comm]

lemma det_keepLeft {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b₀ : Basis ι ℝ E₀) (bE : Basis κ ℝ E)
    (bF : Basis κ ℝ F) (L : E →L[ℝ] F) :
    (LinearMap.toMatrix (b₀.prod bE) (b₀.prod bF) (keepLeft L).toLinearMap).det =
      (LinearMap.toMatrix bE bF L.toLinearMap).det := by
  rw [toMatrix_keepLeft, Matrix.det_fromBlocks_zero₁₂]
  simp

lemma toMatrix_both_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (bE : Basis ι ℝ E) (bF : Basis ι ℝ F)
    (e : ι ≃ κ) (L : E →ₗ[ℝ] F) :
    LinearMap.toMatrix (bE.reindex e) (bF.reindex e) L =
      Matrix.reindex e e (LinearMap.toMatrix bE bF L) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.reindex_apply]

lemma det_both_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (bE : Basis ι ℝ E) (bF : Basis ι ℝ F)
    (e : ι ≃ κ) (L : E →ₗ[ℝ] F) :
    (LinearMap.toMatrix (bE.reindex e) (bF.reindex e) L).det =
      (LinearMap.toMatrix bE bF L).det := by
  rw [toMatrix_both_reindex, Matrix.det_reindex_self]

end Linear
end HydrologyTree
