import HydrologyTree.BlockJacobian
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The Jacobian of a differentiable tangent lift has two copies of the
original Jacobian. Derivative-valued regularity is an explicit proved input
at each later application, not an unproved family Hessian assertion. -/
open Module
noncomputable section
namespace HydrologyTree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def tangentLift (f : E → F) (L : E → E →L[ℝ] F) (x : E × E) : F × F :=
  (f x.1, L x.1 x.2)

def tangentDerivative (L : E → E →L[ℝ] F) (x : E × E) :
    (E × E) →L[ℝ] (F × F) :=
  repeatedBlock (L x.1) ((fderiv ℝ L x.1).flip x.2)

/-- Full tangent-lift derivative, including the second-order off-diagonal block. -/
theorem hasFDerivAt_tangentLift (f : E → F) (L : E → E →L[ℝ] F) (x : E × E)
    (hf : HasFDerivAt f (L x.1) x.1) (hL : DifferentiableAt ℝ L x.1) :
    HasFDerivAt (tangentLift f L) (tangentDerivative L x) x := by
  let P : (E × E) →L[ℝ] E := ContinuousLinearMap.fst ℝ E E
  let Q : (E × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ E E
  have h1 := hf.comp x P.hasFDerivAt
  have h2 := (hL.hasFDerivAt.comp x P.hasFDerivAt).clm_apply Q.hasFDerivAt
  apply (h1.prodMk h2).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · change L x.1 z.2 + (fderiv ℝ L x.1 z.1) x.2 =
      (fderiv ℝ L x.1 z.1) x.2 + L x.1 z.2
    exact add_comm _ _

/-- The determinant is the square without any invertibility assumption. -/
theorem tangentLift_jacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Basis ι ℝ E) (bF : Basis ι ℝ F)
    (f : E → F) (L : E → E →L[ℝ] F) (x : E × E)
    (hf : HasFDerivAt f (L x.1) x.1) (hL : DifferentiableAt ℝ L x.1) :
    (LinearMap.toMatrix (bE.prod bE) (bF.prod bF)
      (fderiv ℝ (tangentLift f L) x).toLinearMap).det =
      (LinearMap.toMatrix bE bF (L x.1).toLinearMap).det ^ 2 := by
  rw [(hasFDerivAt_tangentLift f L x hf hL).fderiv, tangentDerivative,
    det_repeatedBlock]

end HydrologyTree
