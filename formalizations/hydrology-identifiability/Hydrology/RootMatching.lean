import Hydrology.Prony
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots

namespace HydrologyIdentifiability

open scoped BigOperators

noncomputable section

/-- If a nondegenerate finite spectrum satisfies an order-`k` recurrence at
all starting indices, every active rate is a root of the corresponding
characteristic equation. This is the Vandermonde root-extraction step in
Prony's method. -/
theorem finite_spectrum_rates_satisfy_recurrence_polynomial
    {k : ℕ} (w l c : Fin k → ℝ)
    (hw : ∀ i, w i ≠ 0) (hinj : Function.Injective l)
    (hrec : ∀ j : ℕ,
      finiteMoment w l (j + k) =
        ∑ r : Fin k, finiteMoment w l (j + (r : ℕ)) * c r) :
    ∀ i : Fin k, l i ^ k = ∑ r : Fin k, c r * l i ^ (r : ℕ) := by
  have hzero : (fun i : Fin k =>
      w i * (l i ^ k - ∑ r : Fin k, c r * l i ^ (r : ℕ))) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro j
    have hj := hrec (j : ℕ)
    unfold finiteMoment at hj
    have hrewrite :
        (∑ i : Fin k, w i * l i ^ (j : ℕ) *
            (l i ^ k - ∑ r : Fin k, c r * l i ^ (r : ℕ))) =
          (∑ i : Fin k, w i * l i ^ ((j : ℕ) + k)) -
            ∑ r : Fin k, (∑ i : Fin k,
              w i * l i ^ ((j : ℕ) + (r : ℕ))) * c r := by
      simp_rw [pow_add, mul_sub, Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    calc
      (∑ i : Fin k, w i *
          (l i ^ k - ∑ r : Fin k, c r * l i ^ (r : ℕ)) * l i ^ (j : ℕ)) =
          ∑ i : Fin k, w i * l i ^ (j : ℕ) *
            (l i ^ k - ∑ r : Fin k, c r * l i ^ (r : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i : Fin k, w i * l i ^ ((j : ℕ) + k)) -
            ∑ r : Fin k, (∑ i : Fin k,
              w i * l i ^ ((j : ℕ) + (r : ℕ))) * c r := hrewrite
      _ = 0 := sub_eq_zero.mpr hj
  intro i
  have hi := congrFun hzero i
  have hwi : w i ≠ 0 := hw i
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hwi)

end
end HydrologyIdentifiability
