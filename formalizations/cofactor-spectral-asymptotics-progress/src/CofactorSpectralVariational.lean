import CofactorEigenvalueUpper

/-! The variational targets use the actual largest sorted Hermitian eigenvalue. -/
set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem hermitian_shift_posSemidef {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) (l : ℝ)
    (hl : ∀ i, hA.eigenvalues i ≤ l) :
    ((l : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜)-A).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((l-hA.eigenvalues i : ℝ) : 𝕜))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact RCLike.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr (hl i),by simp⟩
  have he : Matrix.diagonal (fun i => ((l-hA.eigenvalues i : ℝ) : 𝕜)) =
      (l : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜)-
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Algebra.algebraMap_eq_smul_one,sub_smul]
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  have h := hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) 𝕜)
  rw [he] at h
  have hs : (l : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜)-A =
      Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        ((l : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜)-
          Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [map_sub,map_smul,map_one,← hA.spectral_theorem]
  rw [hs]
  exact h

theorem hermitian_quadratic_le_eigenvalue_bound {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) (l : ℝ)
    (hl : ∀ i, hA.eigenvalues i ≤ l) (w : Fin N → 𝕜) :
    RCLike.re (star w ⬝ᵥ (A *ᵥ w)) ≤ l*∑ i, ‖w i‖^2 := by
  have h := RCLike.nonneg_iff.mp ((hermitian_shift_posSemidef A hA l hl).dotProduct_mulVec_nonneg w) |>.1
  have he : RCLike.re (star w ⬝ᵥ (((l : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜)-A) *ᵥ w)) =
      l*(∑ i, ‖w i‖^2)-RCLike.re (star w ⬝ᵥ (A *ᵥ w)) := by
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
      dotProduct_smul,RCLike.ofReal_re,RCLike.ofReal_im,RCLike.mul_re,
      RCLike.smul_re,RCLike.smul_im,RCLike.star_def]
    simp [dotProduct,RCLike.mul_re,RCLike.smul_re,RCLike.smul_im,
      RCLike.norm_sq_eq_def,Finset.mul_sum,← Finset.sum_sub_distrib]
  rw [he] at h
  linarith

end
end CofactorSpectral
