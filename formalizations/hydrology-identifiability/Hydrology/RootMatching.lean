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


namespace HydrologyIdentifiability

open scoped BigOperators
open Matrix
open Polynomial

noncomputable section

def charPoly {k : ℕ} (c : Fin k → ℝ) : ℝ[X] :=
  X ^ k - ∑ r : Fin k, C (c r) * X ^ (r : ℕ)

lemma charPoly_monic {k : ℕ} (c : Fin k → ℝ) : (charPoly c).Monic := by
  apply monic_X_pow_sub
  exact degree_sum_fin_lt _

lemma charPoly_natDegree {k : ℕ} (hk : 0 < k) (c : Fin k → ℝ) : (charPoly c).natDegree = k := by
  unfold charPoly
  have hdeg : (∑ r : Fin k, C (c r) * X ^ (r : ℕ)).degree < (k : WithBot ℕ) :=
    degree_sum_fin_lt _
  have hnat : (∑ r : Fin k, C (c r) * X ^ (r : ℕ)).natDegree < k := by
    by_cases hzero : (∑ r : Fin k, C (c r) * X ^ (r : ℕ)) = 0
    · simpa [hzero] using hk
    · exact (natDegree_lt_iff_degree_lt hzero).2 hdeg
  have hnat' : (∑ r : Fin k, C (c r) * X ^ (r : ℕ)).natDegree < ((X : ℝ[X]) ^ k).natDegree := by
    simpa only [natDegree_X_pow] using hnat
  rw [natDegree_sub_eq_left_of_natDegree_lt hnat', natDegree_X_pow]

lemma charPoly_eval_root {k : ℕ} (c l : Fin k → ℝ) (i : Fin k)
    (hroot : l i ^ k = ∑ r : Fin k, c r * l i ^ (r : ℕ)) :
    (charPoly c).eval (l i) = 0 := by
  unfold charPoly
  simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
  rw [← hroot]
  ring

lemma charPoly_roots_image {k : ℕ} (hk : 0 < k) (c l : Fin k → ℝ)
    (hinj : Function.Injective l)
    (hroot : ∀ i, l i ^ k = ∑ r : Fin k, c r * l i ^ (r : ℕ)) :
    (charPoly c).roots.toFinset = Finset.univ.image l := by
  have hsub : Finset.univ.image l ⊆ (charPoly c).roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨(charPoly_monic c).ne_zero, charPoly_eval_root c l i (hroot i)⟩
  symm
  apply (Finset.eq_of_subset_of_card_le hsub)
  calc
    (charPoly c).roots.toFinset.card ≤ (charPoly c).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (charPoly c).natDegree := Polynomial.card_roots' _
    _ = k := charPoly_natDegree hk c
    _ = (Finset.univ.image l).card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp

lemma finite_spectrum_rate_set_identifiable
    {k : ℕ} (hk : 0 < k)
    (w l v m c d : Fin k → ℝ)
    (hw : ∀ i, w i ≠ 0) (hinj : Function.Injective l)
    (hv : ∀ i, v i ≠ 0) (hinj_m : Function.Injective m)
    (hmom : ∀ q : ℕ, q ≤ 2 * k - 1 →
      finiteMoment w l q = finiteMoment v m q)
    (hrec_l : ∀ j : ℕ,
      finiteMoment w l (j + k) =
        ∑ r : Fin k, finiteMoment w l (j + (r : ℕ)) * c r)
    (hrec_m : ∀ j : ℕ,
      finiteMoment v m (j + k) =
        ∑ r : Fin k, finiteMoment v m (j + (r : ℕ)) * d r) :
    Finset.univ.image l = Finset.univ.image m := by
  have hc : c = d := by
    apply two_spectrum_recurrence_coefficients_equal w l v m c d hw hinj hv hinj_m hmom
    · intro j
      exact hrec_l j
    · intro j
      exact hrec_m j
  have hroot_l := finite_spectrum_rates_satisfy_recurrence_polynomial w l c hw hinj hrec_l
  have hroot_m := finite_spectrum_rates_satisfy_recurrence_polynomial v m d hv hinj_m hrec_m
  have hset_l := charPoly_roots_image hk c l hinj hroot_l
  have hset_m := charPoly_roots_image hk d m hinj_m hroot_m
  rw [← hset_l, ← hset_m, hc]


end
end HydrologyIdentifiability
