import APPT.Quantum.SpectralData

open scoped BigOperators ComplexOrder
open Matrix

namespace APPT.Quantum
namespace NecessarySpectrum

/-- The second spectral moment is the actual trace-square, not an added hypothesis. -/
theorem trace_square_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) : (Matrix.diagonal (fun i => (d i : ℂ)) *
      Matrix.diagonal (fun i => (d i : ℂ))).trace.re = ∑ i, (d i)^2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [Complex.mul_re, pow_two]

theorem sum_one (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : IsDensity A) :
    (∑ i, sortedSpectrum n A hA.1.1 i) = 1 := by
  have hd := (density_eigenvalue_diagonal n A hA).2
  rw [Matrix.trace_diagonal] at hd
  have ht : (∑ i, hA.1.1.eigenvalues i) = (1 : ℝ) := by
    exact_mod_cast hd
  exact ((spectralIndex n).sum_comp hA.1.1.eigenvalues).trans ht

theorem purity_eq_sum_sq (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian) :
    purity A = ∑ i, (sortedSpectrum n A hA i)^2 := by
  have hp := purity_unitaryConjugate A (star hA.eigenvectorUnitary)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, actual_diagonalization] at hp
  have hd : purity (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) =
      ∑ i, (hA.eigenvalues i)^2 := trace_square_diagonal _
  exact hp.symm.trans (hd.trans ((spectralIndex n).sum_comp
    (fun i => (hA.eigenvalues i)^2)).symm)

/-- Physical APPT implies both real PSD tests for any nine distinct eigenvalue slots.
No spectral characterization of APPT is assumed in this implication. -/
theorem matrices_posSemidef (n : ℕ) (hn : 3 ≤ n)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian)
    (h : AbsolutelyPPT A) (x : Fin 9 → Fin (3*n)) (hx : Function.Injective x) :
    (matA (sortedSpectrum n A hA ∘ x)).PosSemidef ∧
    (matB (sortedSpectrum n A hA ∘ x)).PosSemidef := by
  let a : Fin 3 → Fin n := Fin.castLE hn
  have ha : Function.Injective a := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin n => k.val) hij)
  exact diagonal_appt_necessary_matrices a ha hA.eigenvalues
    (spectralIndex n ∘ x) ((spectralIndex n).injective.comp hx)
    (appt_eigenvalue_diagonal n A hA h)

end NecessarySpectrum

/-- A complete necessity interface from an actual trace-one PSD APPT matrix.
The spectrum is constructed from the Hermitian spectral theorem; its ordering,
normalization, second moment, and all nine-slot A/B tests are proved here. -/
theorem density_appt_has_sorted_spectrum (n : ℕ) (hn : 3 ≤ n)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (hA : IsDensity A) (h : AbsolutelyPPT A) :
    ∃ lam : Fin (3*n) → ℝ,
      Antitone lam ∧
      (∀ i, 0 ≤ lam i) ∧
      (∑ i, lam i) = 1 ∧
      purity A = ∑ i, (lam i)^2 ∧
      (∀ x : Fin 9 → Fin (3*n), Function.Injective x →
        (matA (lam ∘ x)).PosSemidef ∧ (matB (lam ∘ x)).PosSemidef) := by
  refine ⟨sortedSpectrum n A hA.1.1,
    sortedSpectrum_antitone n A hA.1.1,
    sortedSpectrum_nonneg n A hA.1,
    NecessarySpectrum.sum_one n A hA,
    NecessarySpectrum.purity_eq_sum_sq n A hA.1.1, ?_⟩
  exact NecessarySpectrum.matrices_posSemidef n hn A hA.1.1 h

end APPT.Quantum
