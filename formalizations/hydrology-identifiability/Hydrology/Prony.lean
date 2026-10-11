import Hydrology.WeightIdentifiability
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace HydrologyIdentifiability

open scoped BigOperators
open Matrix

noncomputable section

/-- The finite moment Hankel matrix. -/
def momentHankel {k : ℕ} (w l : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => finiteMoment w l ((i : ℕ) + (j : ℕ))

/-- The weighted Vandermonde factorization of the moment Hankel matrix. -/
theorem momentHankel_factorization {k : ℕ} (w l : Fin k → ℝ) :
    momentHankel w l = (Matrix.vandermonde l)ᵀ *
      (Matrix.diagonal w) * Matrix.vandermonde l := by
  ext i j
  simp [momentHankel, finiteMoment, Matrix.mul_apply, Matrix.vandermonde_apply,
    Matrix.diagonal, pow_add]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The Hankel determinant is the squared Vandermonde determinant times the
product of the output weights. -/
theorem momentHankel_det_factorization {k : ℕ} (w l : Fin k → ℝ) :
    (momentHankel w l).det =
      (Matrix.vandermonde l).det ^ 2 * ∏ i, w i := by
  rw [momentHankel_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- Positive weights and pairwise distinct rates make the finite moment Hankel
matrix nonsingular. -/
theorem momentHankel_det_ne_zero {k : ℕ} (w l : Fin k → ℝ)
    (hw : ∀ i, w i ≠ 0) (hinj : Function.Injective l) :
    (momentHankel w l).det ≠ 0 := by
  rw [momentHankel_det_factorization]
  have hv : (Matrix.vandermonde l).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hprod : (∏ i, w i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => hw i)
  exact mul_ne_zero (pow_ne_zero 2 hv) hprod

end
end HydrologyIdentifiability

namespace HydrologyIdentifiability

/-- A nonsingular Hankel matrix makes a finite-order recurrence coefficient
vector unique from its first `k` recurrence equations. -/
theorem recurrence_coefficients_unique_of_hankel
    {k : ℕ} (μ : ℕ → ℝ) (c d : Fin k → ℝ)
    (hdet : (Matrix.of (fun i j : Fin k => μ ((i : ℕ) + (j : ℕ)))).det ≠ 0)
    (hrec : ∀ j : Fin k,
      (∑ r : Fin k, μ ((j : ℕ) + (r : ℕ)) * c r) =
        ∑ r : Fin k, μ ((j : ℕ) + (r : ℕ)) * d r) :
    c = d := by
  have hz : c - d = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext j
    change (∑ r : Fin k, μ ((j : ℕ) + (r : ℕ)) * (c r - d r)) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hrec j)
  funext i
  have hi := congrFun hz i
  exact sub_eq_zero.mp hi

end HydrologyIdentifiability

namespace HydrologyIdentifiability

/-- For a nondegenerate finite spectrum, the first `k` recurrence equations
have a unique coefficient vector. -/
theorem finite_spectrum_recurrence_unique
    {k : ℕ} (w l c d : Fin k → ℝ)
    (hw : ∀ i, w i ≠ 0) (hinj : Function.Injective l)
    (hrec : ∀ j : Fin k,
      (∑ r : Fin k, finiteMoment w l ((j : ℕ) + (r : ℕ)) * c r) =
        ∑ r : Fin k, finiteMoment w l ((j : ℕ) + (r : ℕ)) * d r) :
    c = d := by
  apply recurrence_coefficients_unique_of_hankel (μ := finiteMoment w l) c d
  · change (momentHankel w l).det ≠ 0
    exact momentHankel_det_ne_zero w l hw hinj
  · exact hrec

end HydrologyIdentifiability
