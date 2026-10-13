import HydrologyTree.EndJacobian

/-! Single-child root coupling, retaining the actual child leak as a linear
function of all child parameters. No leak is assumed constant or nonzero. -/
open Module Matrix
noncomputable section
namespace HydrologyTree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarCouplingFiber (a : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ) + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (a • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma det_scalarCouplingFiber (a : ℝ) : LinearMap.det (scalarCouplingFiber a).toLinearMap = a := by
  let b := (Basis.singleton Unit ℝ).prod (Basis.singleton Unit ℝ)
  have he : LinearMap.toMatrix b b (scalarCouplingFiber a).toLinearMap =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) 1 0 (a • (1 : Matrix Unit Unit ℝ)) := by
    ext i j
    cases i <;> cases j <;> simp [b, LinearMap.toMatrix_apply, scalarCouplingFiber]
  rw [← LinearMap.det_toMatrix b, he, Matrix.det_fromBlocks_zero₂₁]
  simp

def scalarCoupling (a : E →L[ℝ] ℝ) (z : E × (ℝ × ℝ)) : E × (ℝ × ℝ) :=
  (z.1,(z.2.1+z.2.2,a z.1*z.2.2))

def scalarCouplingDerivative (a : E →L[ℝ] ℝ) (z : E × (ℝ × ℝ)) :
    (E × (ℝ × ℝ)) →L[ℝ] (E × (ℝ × ℝ)) :=
  lowerBlock (ContinuousLinearMap.id ℝ E) ((0 : E →L[ℝ] ℝ).prod (z.2.2 • a))
    (scalarCouplingFiber (a z.1))

theorem hasFDerivAt_scalarCoupling (a : E →L[ℝ] ℝ) (z : E × (ℝ × ℝ)) :
    HasFDerivAt (scalarCoupling a) (scalarCouplingDerivative a z) z := by
  let P : (E × (ℝ × ℝ)) →L[ℝ] E := ContinuousLinearMap.fst ℝ E _
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E (ℝ × ℝ))
  let F := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E (ℝ × ℝ))
  have hl := (L.hasFDerivAt (x := z)).add F.hasFDerivAt
  have hc := (a.hasFDerivAt.comp z P.hasFDerivAt).mul F.hasFDerivAt
  apply (P.hasFDerivAt.prodMk (hl.prodMk hc)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change h.2.1 + h.2.2 = 0 + (h.2.1+h.2.2)
      simp
    · change a z.1 * h.2.2 + z.2.2 * a h.1 = z.2.2 * a h.1 + a z.1 * h.2.2
      ring

theorem scalarCoupling_jacobian [FiniteDimensional ℝ E] (a : E →L[ℝ] ℝ)
    (z : E × (ℝ × ℝ)) : endJacobian (scalarCoupling a) z = a z.1 := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_scalarCoupling a z), scalarCouplingDerivative,
    endDet_lowerBlock, det_scalarCouplingFiber]
  simp

end HydrologyTree
