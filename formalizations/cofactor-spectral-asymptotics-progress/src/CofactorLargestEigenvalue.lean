import CofactorSpectralVariational

/-! Explicit largest-eigenvalue bounds and attaining directions for the actual compound. -/
set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder
namespace CofactorSpectral
noncomputable section

def largestHermitianEigenvalue {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨0,by simpa using hn⟩

theorem eigenvalues_le_largest {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) (i : Fin N) :
    hA.eigenvalues i ≤ largestHermitianEigenvalue hn A hA := by
  apply hA.eigenvalues₀_antitone
  exact Nat.zero_le _

theorem largestHermitianEigenvalue_attained {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) :
    ∃ w : Fin N → 𝕜, (∑ j, ‖w j‖^2) = 1 ∧
      RCLike.re (star w ⬝ᵥ (A *ᵥ w)) = largestHermitianEigenvalue hn A hA := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N := Fintype.equivOfCardEq (Fintype.card_fin _)
  let i := e ⟨0,by simpa using hn⟩
  let w := hA.eigenvectorBasis i
  refine ⟨fun j => w j,?_,?_⟩
  · rw [← EuclideanSpace.norm_sq_eq w]
    rw [hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  · rw [← hA.eigenvalues_eq]
    simp only [Matrix.IsHermitian.eigenvalues,i,e,Equiv.symm_apply_apply,largestHermitianEigenvalue]

def largestCompoundRatio {N : ℕ} (hn : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : psdAdmissible A) : ℝ :=
  largestHermitianEigenvalue hn (compound A) (compound_psd A hA.1).isHermitian/A.permanent.re

def largestRealCompoundRatio {N : ℕ} (hn : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : psdAdmissible A) : ℝ :=
  largestHermitianEigenvalue hn (realCompound A) (realCompound_isHermitian A hA.1)/A.permanent.re

theorem complexRayleigh_le_largestCompoundRatio {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) (w : Fin N → ℂ)
    (hw : 0 < vectorNormSq w) : cofactorRayleighRatio A w ≤ largestCompoundRatio hn A hA := by
  have h := hermitian_quadratic_le_eigenvalue_bound (compound A) (compound_psd A hA.1).isHermitian
    _ (eigenvalues_le_largest hn _ _) w
  have he : (∑ i,∑ j,star (w i)*compound A i j*w j).re =
      RCLike.re (star w ⬝ᵥ (compound A *ᵥ w)) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  have hs : vectorNormSq w = ∑ i, ‖w i‖^2 := by simp [vectorNormSq,Complex.normSq_eq_norm_sq]
  unfold cofactorRayleighRatio largestCompoundRatio
  apply (div_le_div_iff₀ (mul_pos hA.2 hw) hA.2).2
  rw [he,hs]
  have hmul := mul_le_mul_of_nonneg_left h hA.2.le
  nlinarith

theorem realRayleigh_le_largestRealCompoundRatio {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) (w : Fin N → ℝ)
    (hw : 0 < vectorNormSq (fun i => (w i : ℂ))) :
    cofactorRayleighRatio A (fun i => (w i : ℂ)) ≤ largestRealCompoundRatio hn A hA := by
  have h := hermitian_quadratic_le_eigenvalue_bound (realCompound A) (realCompound_isHermitian A hA.1)
    _ (eigenvalues_le_largest hn _ _) w
  have he : (∑ i,∑ j,star (w i : ℂ)*compound A i j*(w j : ℂ)).re =
      RCLike.re (star w ⬝ᵥ (realCompound A *ᵥ w)) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,realCompound,Matrix.map,Complex.mul_re]
  have hs : vectorNormSq (fun i => (w i : ℂ)) = ∑ i, ‖w i‖^2 := by
    simp [vectorNormSq,Complex.normSq_ofReal,Real.norm_eq_abs,sq_abs,pow_two]
  unfold cofactorRayleighRatio largestRealCompoundRatio
  apply (div_le_div_iff₀ (mul_pos hA.2 hw) hA.2).2
  rw [he,hs]
  have hmul := mul_le_mul_of_nonneg_left h hA.2.le
  nlinarith

theorem largestCompoundRatio_attained {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) :
    ∃ w : Fin N → ℂ, 0 < vectorNormSq w ∧ cofactorRayleighRatio A w = largestCompoundRatio hn A hA := by
  obtain ⟨w,hs,he⟩ := largestHermitianEigenvalue_attained hn (compound A) (compound_psd A hA.1).isHermitian
  have hw : vectorNormSq w = 1 := by simpa [vectorNormSq,Complex.normSq_eq_norm_sq] using hs
  have hq : (∑ i,∑ j,star (w i)*compound A i j*w j).re =
      RCLike.re (star w ⬝ᵥ (compound A *ᵥ w)) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  exact ⟨w,by rw [hw]; norm_num,by simp only [cofactorRayleighRatio,largestCompoundRatio,hq,he,hw,mul_one]⟩

theorem largestRealCompoundRatio_attained {N : ℕ} (hn : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : psdAdmissible A) :
    ∃ w : Fin N → ℝ, 0 < vectorNormSq (fun i => (w i : ℂ)) ∧
      cofactorRayleighRatio A (fun i => (w i : ℂ)) = largestRealCompoundRatio hn A hA := by
  obtain ⟨w,hs,he⟩ := largestHermitianEigenvalue_attained hn (realCompound A) (realCompound_isHermitian A hA.1)
  have hw : vectorNormSq (fun i => (w i : ℂ)) = 1 := by
    simpa [vectorNormSq,Complex.normSq_ofReal,Real.norm_eq_abs,sq_abs,pow_two] using hs
  have hq : (∑ i,∑ j,star (w i : ℂ)*compound A i j*(w j : ℂ)).re =
      RCLike.re (star w ⬝ᵥ (realCompound A *ᵥ w)) := by
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,realCompound,Matrix.map,Complex.mul_re]
  exact ⟨w,by rw [hw]; norm_num,by simp only [cofactorRayleighRatio,largestRealCompoundRatio,hq,he,hw,mul_one]⟩

end
end CofactorSpectral
