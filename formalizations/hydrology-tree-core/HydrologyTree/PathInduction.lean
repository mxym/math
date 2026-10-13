import HydrologyTree.PathPhysical
import HydrologyTree.PathNormalization
import HydrologyTree.ScalarCoupling

/-! Complete all-size determinant induction for the actual endpoint-path
characteristic/cofactor coefficient map. Every rate value, including zero,
is allowed; all coordinate changes are explicit linear permutations. -/
open Polynomial Matrix Module
noncomputable section
namespace HydrologyTree

/-- The actual physical coefficient map, merely put in a common coordinate order. -/
def normalizedPhysicalPath (n : ℕ) (z : PathRates n) : PathRates n :=
  pathCoefficientEquiv n (pathCoefficientMap n (pathRateEquiv n z))

lemma normalizedPhysicalPath_zero : normalizedPhysicalPath 0 = id := by
  funext a
  letI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1))
  change ((cut 1 (physicalCharacteristic (pathTree 0) (singletonRateEquiv a)) : Coeff 1) : ℝ[X]).coeff 0 = a
  rw [cut_coeff 1 _ (⟨0, by omega⟩ : Fin 1)]
  rw [physicalCharacteristic, Matrix.charpoly,
    Matrix.det_eq_elem_of_subsingleton _ (0 : Fin (0+1))]
  simp [Matrix.charmatrix_apply_eq, compartmentMatrix, singletonRateEquiv]

@[simp] lemma pathTransitionEquiv_apply (n : ℕ) (z : PathRates (n+1)) :
    pathTransitionEquiv n z =
      (((pathCoefficientEquiv n).symm z.1).1, (z.2,((pathCoefficientEquiv n).symm z.1).2)) := rfl

/-- The genuine physical recursion factors through the proved local maps. -/
theorem normalizedPhysicalPath_succ (n : ℕ) (z : PathRates (n+1)) :
    normalizedPhysicalPath (n+1) z = normalizedPathStep n
      (keepFunction (normalizedPhysicalPath n) (scalarCoupling (pathLeak n) z)) := by
  unfold normalizedPhysicalPath
  rw [pathRateEquiv_succ, pathCoefficientMap_recursion]
  unfold normalizedPathStep keepFunction scalarCoupling
  rw [pathTransitionEquiv_apply]
  simp only [LinearEquiv.symm_apply_apply, pathLeak_apply]

lemma normalizedPhysicalPath_succ_fun (n : ℕ) :
    normalizedPhysicalPath (n+1) = normalizedPathStep n ∘
      (keepFunction (F := ℝ × ℝ) (normalizedPhysicalPath n) ∘ scalarCoupling (pathLeak n)) := by
  funext z
  exact normalizedPhysicalPath_succ n z

/-- Differentiability of the actual full coefficient map is proved by size induction. -/
theorem differentiable_normalizedPhysicalPath (n : ℕ) : Differentiable ℝ (normalizedPhysicalPath n) := by
  induction n with
  | zero => rw [normalizedPhysicalPath_zero]; exact differentiable_id
  | succ n ih =>
    rw [normalizedPhysicalPath_succ_fun]
    intro z
    have hc := (hasFDerivAt_scalarCoupling (pathLeak n) z).differentiableAt
    have hk := (hasFDerivAt_keepFunction (scalarCoupling (pathLeak n) z) (ih z.1)).differentiableAt
    exact (differentiable_normalizedPathStep n _).comp z (hk.comp z hc)

/-- Exact one-step Jacobian recurrence, without inversion of any parameter. -/
theorem normalizedPhysicalPath_jacobian_succ (n : ℕ) (z : PathRates (n+1)) :
    endJacobian (normalizedPhysicalPath (n+1)) z =
      (-1 : ℝ)^(n+1) * (pathLeak n z.1)^(n+1) * z.2.2^n *
        endJacobian (normalizedPhysicalPath n) z.1 := by
  have hc := (hasFDerivAt_scalarCoupling (pathLeak n) z).differentiableAt
  have hk := (hasFDerivAt_keepFunction (scalarCoupling (pathLeak n) z)
    (differentiable_normalizedPhysicalPath n z.1)).differentiableAt
  rw [normalizedPhysicalPath_succ_fun,
    endJacobian_comp (differentiable_normalizedPathStep n _) (hk.comp z hc),
    endJacobian_comp hk hc, normalizedPathStep_jacobian,
    endJacobian_keepFunction (normalizedPhysicalPath n) (scalarCoupling (pathLeak n) z)
      (differentiable_normalizedPhysicalPath n z.1),
    scalarCoupling_jacobian]
  change (-1 : ℝ)^(n+1) * (pathLeak n z.1 * z.2.2)^n *
      (endJacobian (normalizedPhysicalPath n) z.1 * pathLeak n z.1) = _
  rw [mul_pow, pow_succ]
  ring

/-- Complete all-size monomial formula for the actual endpoint catenary.
No assumption of the target determinant or of any intermediate recurrence. -/
theorem normalizedPhysicalPath_jacobian (n : ℕ) (z : PathRates n) :
    endJacobian (normalizedPhysicalPath n) z = pathOrientation n * pathWeight n z := by
  induction n with
  | zero =>
    rw [normalizedPhysicalPath_zero, endJacobian]
    simp [pathOrientation, pathWeight]
  | succ n ih =>
    rw [normalizedPhysicalPath_jacobian_succ, ih, pathOrientation, pathWeight]
    ring

/-- Recover the unnormalized actual coefficient map by inverse permutations. -/
lemma pathCoefficientMap_from_normalized (n : ℕ) : pathCoefficientMap n =
    fun x => (pathCoefficientEquiv n).symm (normalizedPhysicalPath n ((pathRateEquiv n).symm x)) := by
  funext x
  simp [normalizedPhysicalPath]

theorem differentiable_pathCoefficientMap (n : ℕ) : Differentiable ℝ (pathCoefficientMap n) := by
  rw [pathCoefficientMap_from_normalized]
  intro x
  exact (pathCoefficientEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp x
    ((differentiable_normalizedPhysicalPath n _).comp x
      (pathRateEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt)

end HydrologyTree
