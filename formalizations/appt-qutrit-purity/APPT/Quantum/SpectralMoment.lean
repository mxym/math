import APPT.Quantum.Basic
import Mathlib.Analysis.Matrix.Spectrum
open scoped BigOperators ComplexOrder
open Matrix

namespace APPT.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_square_eq_eigenvalues_square
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A*A).trace = ∑ i : ι, (hA.eigenvalues i : ℂ)^2 := by
  let U : Matrix.unitaryGroup ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hAU : A = (U : Matrix ι ι ℂ)*D*(U : Matrix ι ι ℂ)ᴴ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.spectral_theorem
  have hU : (U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ)=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  have hs :
      ((U : Matrix ι ι ℂ)*D*(U : Matrix ι ι ℂ)ᴴ)*
        ((U : Matrix ι ι ℂ)*D*(U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ)*(D*D)*(U : Matrix ι ι ℂ)ᴴ := by
    calc
      _ = (U : Matrix ι ι ℂ)*D*((U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ))*D*(U : Matrix ι ι ℂ)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp [Matrix.mul_assoc]
  calc
    (A*A).trace = ((U : Matrix ι ι ℂ)*(D*D)*(U : Matrix ι ι ℂ)ᴴ).trace := by
      rw [hAU, hs]
    _ = (D*D).trace := by
      rw [Matrix.trace_mul_cycle, hU]
      simp
    _ = ∑ i : ι, (hA.eigenvalues i : ℂ)^2 := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      simp [D, pow_two]

variable {b : Type*} [Fintype b] [DecidableEq b]

/-- Quantum purity equals the sum of the squares of real eigenvalues. -/
theorem purity_eq_sum_eigenvalues_sq
    (A : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) (hA : A.IsHermitian) :
    purity A = ∑ i, (hA.eigenvalues i)^2 := by
  unfold purity
  rw [trace_square_eq_eigenvalues_square A hA]
  have hc : (∑ i, (hA.eigenvalues i : ℂ)^2) =
      (((∑ i, (hA.eigenvalues i)^2) : ℝ) : ℂ) := by
    push_cast
    rfl
  exact (congrArg Complex.re hc).trans (by simp only [← Complex.ofReal_pow, Complex.ofReal_re])

/-- For a density matrix, the actual Hermitian eigenvalues sum to one. -/
theorem density_eigenvalues_sum_one
    (A : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) (hA : IsDensity A) :
    (∑ i, hA.1.1.eigenvalues i) = 1 := by
  have htrace := hA.1.1.trace_eq_sum_eigenvalues
  have hc : (∑ i, (hA.1.1.eigenvalues i : ℂ)) = (1 : ℂ) := htrace.symm.trans hA.2
  exact_mod_cast hc

end APPT.Quantum
