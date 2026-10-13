import HydrologyTree.Triangular
import Mathlib.LinearAlgebra.Determinant

/-! Basis-independent determinant calculus for the actual finite-dimensional
Fréchet derivative. Used after explicit coefficient permutation equivalences. -/
open Module
noncomputable section
namespace HydrologyTree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Determinant of the actual derivative of an endomorphism. -/
def endJacobian (f : E → E) (x : E) : ℝ := LinearMap.det (fderiv ℝ f x).toLinearMap

lemma endJacobian_of_hasFDerivAt {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasFDerivAt f L x) : endJacobian f x = LinearMap.det L.toLinearMap := by
  rw [endJacobian, hf.fderiv]

theorem endJacobian_comp {f g : E → E} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    endJacobian (f ∘ g) x = endJacobian f (g x) * endJacobian g x := by
  rw [endJacobian, (hf.hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
  exact LinearMap.det_comp _ _

/-- Conjugation transports coordinates without changing the derivative determinant. -/
theorem endJacobian_conjugate (e : E ≃L[ℝ] F) (f : E → E) (x : F)
    (hf : DifferentiableAt ℝ f (e.symm x)) :
    endJacobian (fun z => e (f (e.symm z))) x = endJacobian f (e.symm x) := by
  have h := e.toContinuousLinearMap.hasFDerivAt.comp x
    (hf.hasFDerivAt.comp x e.symm.toContinuousLinearMap.hasFDerivAt)
  have he : fderiv ℝ (fun z => e (f (e.symm z))) x =
      e.toContinuousLinearMap.comp ((fderiv ℝ f (e.symm x)).comp e.symm.toContinuousLinearMap) := h.fderiv
  rw [endJacobian, he]
  change LinearMap.det (e.toLinearEquiv.toLinearMap.comp
    ((fderiv ℝ f (e.symm x)).toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)) = _
  exact LinearMap.det_conj _ e.toLinearEquiv

/-- Triangular block determinant, independent of the choice of bases. -/
lemma endDet_lowerBlock [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] E) (C : E →L[ℝ] F) (M : F →L[ℝ] F) :
    LinearMap.det (lowerBlock L C M).toLinearMap =
      LinearMap.det L.toLinearMap * LinearMap.det M.toLinearMap := by
  simpa only [LinearMap.det_toMatrix] using
    det_lowerBlock (Module.finBasis ℝ E) (Module.finBasis ℝ F) L C M

/-- A map on the first factor and identity on the second factor. -/
def keepFunction (f : E → E) (z : E × F) : E × F := (f z.1,z.2)

lemma hasFDerivAt_keepFunction {f : E → E} (x : E × F)
    (hf : DifferentiableAt ℝ f x.1) :
    HasFDerivAt (keepFunction (F := F) f)
      ((fderiv ℝ f x.1).prodMap (ContinuousLinearMap.id ℝ F)) x := by
  exact (hf.hasFDerivAt.comp x (ContinuousLinearMap.fst ℝ E F).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℝ E F).hasFDerivAt

lemma endJacobian_keepFunction [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → E) (x : E × F) (hf : DifferentiableAt ℝ f x.1) :
    endJacobian (keepFunction (F := F) f) x = endJacobian f x.1 := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_keepFunction x hf)]
  change LinearMap.det (LinearMap.prodMap (fderiv ℝ f x.1).toLinearMap (LinearMap.id : F →ₗ[ℝ] F)) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  rfl

end HydrologyTree
