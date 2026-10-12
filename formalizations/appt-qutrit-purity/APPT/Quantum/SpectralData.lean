import APPT.Quantum.CornerNecessity
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

theorem product_card (n : ℕ) : Fintype.card (Fin 3 × Fin n)=3*n := by simp

/-- This reindexing is the same one used in Mathlib's sorted spectral theorem. -/
noncomputable def spectralIndex (n : ℕ) : Fin (3*n) ≃ (Fin 3 × Fin n) :=
  (finCongr (product_card n).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 3 × Fin n))))

noncomputable def sortedSpectrum (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian) :
    Fin (3*n) → ℝ := hA.eigenvalues ∘ spectralIndex n

theorem sortedSpectrum_eq (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian)
    (i : Fin (3*n)) : sortedSpectrum n A hA i =
    hA.eigenvalues₀ (Fin.cast (product_card n).symm i) := by
  simp [sortedSpectrum, spectralIndex, Matrix.IsHermitian.eigenvalues]

theorem sortedSpectrum_antitone (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian) :
    Antitone (sortedSpectrum n A hA) := by
  intro i j hij
  rw [sortedSpectrum_eq,sortedSpectrum_eq]
  exact hA.eigenvalues₀_antitone hij

theorem sortedSpectrum_nonneg (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.PosSemidef) :
    ∀ i, 0 ≤ sortedSpectrum n A hA.1 i := by
  intro i
  exact hA.eigenvalues_nonneg (spectralIndex n i)

theorem actual_diagonalization (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)ᴴ*A*
      (hA.eigenvectorUnitary : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) =
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  convert h using 1 <;> rfl

theorem appt_eigenvalue_diagonal (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian)
    (h : AbsolutelyPPT A) :
    AbsolutelyPPT (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := by
  have h' := absolutelyPPT_conjugate h (star hA.eigenvectorUnitary)
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, actual_diagonalization] using h'

theorem density_eigenvalue_diagonal (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : IsDensity A) :
    IsDensity (Matrix.diagonal (fun i => (hA.1.1.eigenvalues i : ℂ))) := by
  have h' := isDensity_unitaryConjugate hA (star hA.1.1.eigenvectorUnitary)
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, actual_diagonalization] using h'

end APPT.Quantum
