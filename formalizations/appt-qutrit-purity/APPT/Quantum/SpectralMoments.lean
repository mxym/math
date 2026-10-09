import APPT.Quantum.SpectralData
import APPT.SpectralConditions
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

theorem purity_diagonal_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) : (Matrix.diagonal (fun i => (d i : ℂ))*
      Matrix.diagonal (fun i => (d i : ℂ))).trace.re = ∑ i, (d i)^2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [Complex.mul_re, pow_two]

theorem sortedSpectrum_sum_one (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : IsDensity A) :
    (∑ i, sortedSpectrum n A hA.1.1 i) = 1 := by
  have hd := (density_eigenvalue_diagonal n A hA).2
  rw [Matrix.trace_diagonal] at hd
  have ht : (∑ i, hA.1.1.eigenvalues i) = (1 : ℝ) := by
    exact_mod_cast hd
  exact ((spectralIndex n).sum_comp hA.1.1.eigenvalues).trans ht

theorem purity_eq_sortedSpectrum (n : ℕ)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian) :
    purity A = ∑ i, (sortedSpectrum n A hA i)^2 := by
  have hp := purity_unitaryConjugate A (star hA.eigenvectorUnitary)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, actual_diagonalization] at hp
  have hdiag : purity (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) =
      ∑ i, (hA.eigenvalues i)^2 := purity_diagonal_real _
  exact hp.symm.trans (hdiag.trans ((spectralIndex n).sum_comp
    (fun i => (hA.eigenvalues i)^2)).symm)

/-- The real sorted eigenvalues of every actual APPT state satisfy the physical corner tests. -/
theorem sortedSpectrum_cornerConditions (n : ℕ) (hn : 3 ≤ n)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hA : A.IsHermitian)
    (h : AbsolutelyPPT A) : CornerConditions (sortedSpectrum n A hA) := by
  intro x hx
  let a : Fin 3 → Fin n := Fin.castLE hn
  have ha : Function.Injective a := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin n => k.val) hij)
  have hq := diagonal_appt_necessary_matrices a ha hA.eigenvalues
    (spectralIndex n ∘ x) ((spectralIndex n).injective.comp hx)
    (appt_eigenvalue_diagonal n A hA h)
  exact hq

end APPT.Quantum
