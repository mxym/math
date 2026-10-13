import HydrologyTree.EndJacobian
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Actual determinant calculus for a scalar slot multiplied by a function of
remaining coordinates, with those coordinates kept fixed. -/
open Matrix Module
noncomputable section
namespace HydrologyTree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def upperBlock (L : E →L[ℝ] E) (C : F →L[ℝ] E) (M : F →L[ℝ] F) : (E × F) →L[ℝ] (E × F) :=
  (L.comp (ContinuousLinearMap.fst ℝ E F)+C.comp (ContinuousLinearMap.snd ℝ E F)).prod
    (M.comp (ContinuousLinearMap.snd ℝ E F))

lemma endDet_upperBlock [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] E) (C : F →L[ℝ] E) (M : F →L[ℝ] F) :
    LinearMap.det (upperBlock L C M).toLinearMap=LinearMap.det L.toLinearMap*LinearMap.det M.toLinearMap := by
  let bE := Module.finBasis ℝ E
  let bF := Module.finBasis ℝ F
  have hmat : LinearMap.toMatrix (bE.prod bF) (bE.prod bF) (upperBlock L C M).toLinearMap=
      Matrix.fromBlocks (LinearMap.toMatrix bE bE L.toLinearMap) (LinearMap.toMatrix bF bE C.toLinearMap)
        0 (LinearMap.toMatrix bF bF M.toLinearMap) := by
    ext i j
    cases i <;> cases j <;> simp [LinearMap.toMatrix_apply,upperBlock]
  rw [← LinearMap.det_toMatrix (bE.prod bF),hmat,Matrix.det_fromBlocks_zero₂₁]
  simp only [LinearMap.det_toMatrix]

def scalarSlotScale (f : E → ℝ) (z : ℝ × E) : ℝ × E := (z.1*f z.2,z.2)

def scalarSlotDerivative (f : E → ℝ) (z : ℝ × E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  upperBlock (f z.2 • ContinuousLinearMap.id ℝ ℝ)
    (z.1 • fderiv ℝ f z.2) (ContinuousLinearMap.id ℝ E)

lemma hasFDerivAt_scalarSlotScale (f : E → ℝ) (z : ℝ × E) (hf : DifferentiableAt ℝ f z.2) :
    HasFDerivAt (scalarSlotScale f) (scalarSlotDerivative f z) z := by
  let P : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E
  let Q : (ℝ × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ ℝ E
  have h := (P.hasFDerivAt.mul (hf.hasFDerivAt.comp z Q.hasFDerivAt)).prodMk Q.hasFDerivAt
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [P,Q,scalarSlotDerivative,upperBlock]
    ring
  · rfl

/-- The actual first-coordinate derivative is f(v), even when f(v)=0.
No nonsingularity is assumed to prove the block determinant identity. -/
theorem scalarSlotScale_jacobian [FiniteDimensional ℝ E] (f : E → ℝ) (z : ℝ × E)
    (hf : DifferentiableAt ℝ f z.2) : endJacobian (scalarSlotScale f) z=f z.2 := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_scalarSlotScale f z hf),scalarSlotDerivative,endDet_upperBlock]
  change LinearMap.det (f z.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))*LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)=_
  simp [LinearMap.det_smul]

/-- Add a multiple of the scalar first coordinate to a fixed vector slot. -/
def scalarVectorShear (v : E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  lowerBlock (ContinuousLinearMap.id ℝ ℝ)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v) (ContinuousLinearMap.id ℝ E)

@[simp] lemma scalarVectorShear_apply (v : E) (z : ℝ × E) :
    scalarVectorShear v z=(z.1,z.1 • v+z.2) := rfl

lemma scalarVectorShear_jacobian [FiniteDimensional ℝ E] (v : E) (z : ℝ × E) :
    endJacobian (scalarVectorShear v) z=1 := by
  rw [endJacobian_of_hasFDerivAt (scalarVectorShear v).hasFDerivAt,scalarVectorShear,endDet_lowerBlock]
  simp

end HydrologyTree
