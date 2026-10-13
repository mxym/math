import HydrologyTree.EndJacobian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Coordinate transport stated for finite-dimensional linear equivalences.
Keeping this proof generic avoids expanding tree-specific coordinate instances
while checking compositions of the actual Frechet derivative. -/
noncomputable section
namespace HydrologyTree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma differentiable_linear_conjugate (e : E ≃ₗ[ℝ] F) (f : F → F)
    (hf : Differentiable ℝ f) : Differentiable ℝ (fun z : E => e.symm (f (e z))) := by
  exact e.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiable.comp
    (hf.comp e.toContinuousLinearEquiv.toContinuousLinearMap.differentiable)

lemma endJacobian_linear_conjugate (e : E ≃ₗ[ℝ] F) (f : F → F) (x : E)
    (hf : DifferentiableAt ℝ f (e x)) :
    endJacobian (fun z : E => e.symm (f (e z))) x = endJacobian f (e x) := by
  exact endJacobian_conjugate e.symm.toContinuousLinearEquiv f x hf

end HydrologyTree
