import CofactorExtremaUpper
import Mathlib.Analysis.Matrix.Spectrum

/-! Standard Hermitian eigenvalues of the actual compound, and of its entrywise real part. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

def realCompound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  (compound A).map Complex.re

theorem realCompound_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) : (realCompound A).IsHermitian := by
  apply (compound_psd A hA).isHermitian.map Complex.re
  intro z
  simp [Complex.star_def]

theorem compound_eigenvalue_harmonic_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : psdAdmissible A) (i : Fin n) :
    (compound_psd A hA.1).isHermitian.eigenvalues i / A.permanent.re ≤
      4 + (harmonic (n-1) : ℝ) := by
  let hC := (compound_psd A hA.1).isHermitian
  let w := hC.eigenvectorBasis i
  have hw : vectorNormSq (fun j => w j) = 1 := by
    unfold vectorNormSq
    simp_rw [Complex.normSq_eq_norm_sq]
    rw [← EuclideanSpace.norm_sq_eq w]
    have hn : ‖w‖ = 1 := hC.eigenvectorBasis.orthonormal.1 i
    rw [hn]
    norm_num
  have he : (∑ j,∑ k,star (w j) * compound A j k * w k).re = hC.eigenvalues i := by
    rw [hC.eigenvalues_eq]
    change Complex.re _ = Complex.re _
    simp [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    rfl
  have h := cofactorRayleighRatio_complex_harmonic_upper A hA (fun j => w j)
    (by rw [hw]; norm_num)
  simpa only [cofactorRayleighRatio,he,hw,mul_one] using h

theorem realCompound_eigenvalue_harmonic_upper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : psdAdmissible A) (i : Fin n) :
    (realCompound_isHermitian A hA.1).eigenvalues i / A.permanent.re ≤
      2 + (harmonic (n-1) : ℝ)/2 := by
  let hC := realCompound_isHermitian A hA.1
  let x := hC.eigenvectorBasis i
  have hx : vectorNormSq (fun j => (x j : ℂ)) = 1 := by
    unfold vectorNormSq
    simp_rw [Complex.normSq_ofReal,← pow_two]
    rw [← EuclideanSpace.real_norm_sq_eq x]
    have hn : ‖x‖ = 1 := hC.eigenvectorBasis.orthonormal.1 i
    rw [hn]
    norm_num
  have he : (∑ j,∑ k,star (x j : ℂ) * compound A j k * (x k : ℂ)).re =
      hC.eigenvalues i := by
    rw [hC.eigenvalues_eq]
    change Complex.re _ = _
    simp [dotProduct,Matrix.mulVec,realCompound,Matrix.map,Complex.mul_re,
      Finset.mul_sum,mul_assoc]
    rfl
  have h := cofactorRayleighRatio_real_harmonic_upper A hA (fun j => x j)
    (by rw [hx]; norm_num)
  simpa only [cofactorRayleighRatio,he,hx,mul_one] using h

end
end CofactorSpectral
