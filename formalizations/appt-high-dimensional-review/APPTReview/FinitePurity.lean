import APPTReview.SpectralBaseline

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Actual quantum purity equals the second moment of the canonically ordered eigenvalues. -/
theorem purity_eq_ordered_eigenvalues {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) :
    APPT.Quantum.purity A = ∑ i, (hA.eigenvalues₀ i)^2 := by
  have hu := APPT.Quantum.purity_unitaryConjugate A (star hA.eigenvectorUnitary)
  have hd := hA.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at hd hu
  rw [hd] at hu
  have he : APPT.Quantum.purity (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) =
      ∑ i, (hA.eigenvalues i)^2 := by
    unfold APPT.Quantum.purity
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [Complex.mul_re, pow_two]
  have hs := (spectralLabel (a × b)).sum_comp (fun i => (hA.eigenvalues i)^2)
  simp only [eigenvalues_spectralLabel] at hs
  exact hu.symm.trans (he.trans hs.symm)

/-- The unrestricted finite purity bound for actual APPT density matrices.
The normalizer is the genuine paper pivot; no graph or variance premise is supplied. -/
theorem density_appt_finite_purity_bound {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    APPT.Quantum.purity A-1/(((h+1 : ℕ) : ℝ)*n) ≤
      max 8 (4+((h+1 : ℕ) : ℝ)*n/(h : ℝ)^2)*
        (hρ.1.isHermitian.eigenvalues₀ (pairedPivot (by omega) hmn))^2 := by
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  simpa using density_appt_ordered_variance_bound hh hmn hρ happt

end APPTReview
