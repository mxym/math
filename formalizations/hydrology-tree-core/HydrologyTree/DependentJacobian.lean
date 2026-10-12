import HydrologyTree.EndJacobian
import HydrologyTree.DependentBlocks

/-! The actual derivative determinant of independent children of different
sizes. The module proves, rather than assumes, heterogeneous Jacobian multiplication. -/
open Module Matrix
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [LinearOrder I]
variable {E : I → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

def dependentPiEnd (f : (i : I) → E i → E i) (z : (i : I) → E i) : (i : I) → E i :=
  fun i => f i (z i)

def dependentPiFDeriv (f : (i : I) → E i → E i) (z : (i : I) → E i) :
    ((i : I) → E i) →L[ℝ] ((i : I) → E i) :=
  ContinuousLinearMap.pi fun i => (fderiv ℝ (f i) (z i)).comp (ContinuousLinearMap.proj i)

theorem hasFDerivAt_dependentPiEnd (f : (i : I) → E i → E i) (z : (i : I) → E i)
    (hf : ∀ i, DifferentiableAt ℝ (f i) (z i)) :
    HasFDerivAt (dependentPiEnd f) (dependentPiFDeriv f z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hf i).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : ((j : I) → E j) →L[ℝ] E i).hasFDerivAt

lemma determinant_dependentPi (L : (i : I) → E i →ₗ[ℝ] E i) :
    (LinearMap.pi (fun i => (L i).comp (LinearMap.proj i))).det = ∏ i : I, (L i).det := by
  let b := fun i : I => Module.finBasis ℝ (E i)
  have hM : LinearMap.toMatrix (Pi.basis b) (Pi.basis b)
      (LinearMap.pi (fun i => (L i).comp (LinearMap.proj i))) =
      Matrix.blockDiagonal' (fun i => LinearMap.toMatrix (b i) (b i) (L i)) := by
    ext ⟨i,a⟩ ⟨j,c⟩
    by_cases h : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr]
    · simp [LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr,
        Matrix.blockDiagonal'_apply_ne, h, Ne.symm h]
  rw [← LinearMap.det_toMatrix (Pi.basis b), hM, det_dependent_blocks]
  exact Finset.prod_congr rfl (fun i _ => LinearMap.det_toMatrix (b i) (L i))

/-- The full Fréchet determinant of the actual independent-child transformation. -/
theorem endJacobian_dependentPiEnd (f : (i : I) → E i → E i) (z : (i : I) → E i)
    (hf : ∀ i, DifferentiableAt ℝ (f i) (z i)) :
    endJacobian (dependentPiEnd f) z = ∏ i : I, endJacobian (f i) (z i) := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_dependentPiEnd f z hf)]
  exact determinant_dependentPi (fun i => (fderiv ℝ (f i) (z i)).toLinearMap)

end HydrologyTree
