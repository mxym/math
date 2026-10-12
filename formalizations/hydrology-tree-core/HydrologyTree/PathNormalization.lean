import HydrologyTree.PathRates

/-! Explicit coordinate permutations for the endpoint-path coefficient map.
The normalization reads existing coefficients; it does not divide, rescale,
fit, or impose the desired Jacobian as an assumption. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

/-- Rearrange p,(d,c),q into (p,q),(d,c). -/
def pathShuffle (n : ℕ) : PathPolyData n ≃ₗ[ℝ] (PathCoefficients n × (ℝ × ℝ)) where
  toFun z := ((z.1,z.2.2),z.2.1)
  invFun z := (z.1.1,(z.2,z.1.2))
  left_inv z := rfl
  right_inv z := rfl
  map_add' z w := rfl
  map_smul' a z := rfl

/-- A degree-one monic polynomial has just one non-leading coefficient. -/
def baseCoefficientEquiv : PathCoefficients 0 ≃ₗ[ℝ] ℝ where
  toFun z := (z.1 : ℝ[X]).coeff 0
  invFun a := (cut 1 (C a),0)
  left_inv z := by
    apply Prod.ext
    · apply (degreeLTEquiv ℝ 1).injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change ((cut 1 (C ((z.1 : ℝ[X]).coeff 0)) : Coeff 1) : ℝ[X]).coeff 0 = _
      rw [cut_coeff 1 _ (⟨0, by omega⟩ : Fin 1)]
      simp
    · apply (degreeLTEquiv ℝ 0).injective
      funext i
      exact Fin.elim0 i
  right_inv a := by
    change ((cut 1 (C a) : Coeff 1) : ℝ[X]).coeff 0 = a
    rw [cut_coeff 1 (C a) (⟨0, by omega⟩ : Fin 1)]
    simp
  map_add' z w := by simp
  map_smul' a z := by simp

/-- The order of all original coefficient coordinates, recursively permuted. -/
def pathCoefficientEquiv : (n : ℕ) → PathCoefficients n ≃ₗ[ℝ] PathRates n
  | 0 => baseCoefficientEquiv
  | n+1 => (parentCoefficientEquiv n).trans (pathShuffle n) |>.trans
      ((pathCoefficientEquiv n).prodCongr (LinearEquiv.refl ℝ (ℝ × ℝ)))

/-- From normalized child coefficients and (d,c) to the local polynomial data. -/
def pathTransitionEquiv (n : ℕ) : PathRates (n+1) ≃ₗ[ℝ] PathPolyData n :=
  (((pathCoefficientEquiv n).symm.prodCongr (LinearEquiv.refl ℝ (ℝ × ℝ)))).trans
    (pathShuffle n).symm

lemma pathCoefficientEquiv_succ (n : ℕ) (p : PathCoefficients (n+1)) :
    pathCoefficientEquiv (n+1) p = (pathTransitionEquiv n).symm (parentCoefficientEquiv n p) := rfl

/-- The actual one-child coefficient operation in the explicit common order. -/
def normalizedPathStep (n : ℕ) (z : PathRates (n+1)) : PathRates (n+1) :=
  pathCoefficientEquiv (n+1) (pathStepCoefficients (pathTransitionEquiv n z))

lemma normalizedPathStep_conjugate (n : ℕ) : normalizedPathStep n =
    fun z => (pathTransitionEquiv n).symm
      (rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n) (pathTransitionEquiv n z)) := by
  funext z
  rw [normalizedPathStep, pathCoefficientEquiv_succ, parentCoefficient_step_eq]

/-- Smoothness follows from the actual polynomial root operation. -/
theorem differentiable_normalizedPathStep (n : ℕ) : Differentiable ℝ (normalizedPathStep n) := by
  rw [normalizedPathStep_conjugate]
  intro z
  exact (pathTransitionEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp z
    ((hasFDerivAt_rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n)
      (pathTransitionEquiv n z)).differentiableAt.comp z
        (pathTransitionEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt)

theorem normalizedPathStep_jacobian (n : ℕ) (z : PathRates (n+1)) :
    endJacobian (normalizedPathStep n) z = (-1 : ℝ)^(n+1) * z.2.2^n := by
  rw [normalizedPathStep_conjugate]
  have h := endJacobian_conjugate (pathTransitionEquiv n).symm.toContinuousLinearEquiv
    (rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n)) z
    (hasFDerivAt_rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n)
      (pathTransitionEquiv n z)).differentiableAt
  change endJacobian (fun z => (pathTransitionEquiv n).symm
      (rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n) (pathTransitionEquiv n z))) z = _ at h
  rw [h, endJacobian_rootTransition, finrank_coeff]
  rfl

end HydrologyTree
