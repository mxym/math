import BapatRepetition
import BapatRealPolynomial
import Mathlib.Data.Fintype.Sort

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

noncomputable section

variable {ι κ C R : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype κ] [LinearOrder κ] [Fintype C] [LinearOrder C] [CommRing R]

theorem formsProduct_comp (e : ι ≃ κ) (v : κ → C → R) :
    formsProduct (fun i => v (e i)) = formsProduct v := by
  exact e.prod_comp (fun i => linearForm (v i))

theorem remainingPolynomial_comp (e : ι ≃ κ) (v : κ → C → R) (i j : ι) :
    remainingPolynomial (fun k => v (e k)) i j = remainingPolynomial v (e i) (e j) := by
  simp only [remainingPolynomial_eq_deleteTwoProduct]
  exact deleteTwoProduct_comp e (fun k => linearForm (v k)) i j

/-- Only increasing relabelings preserve this ordered wedge sum. -/
theorem wedgePolynomial_orderIso (e : ι ≃o κ) (v : κ → C → R) (a b : C) :
    wedgePolynomial (fun i => v (e i)) a b = wedgePolynomial v a b := by
  classical
  unfold wedgePolynomial
  simp only [originalPairs, Finset.sum_filter]
  have hr (i j : ι) : remainingPolynomial (fun k => v (e k)) i j =
      remainingPolynomial v (e i) (e j) := remainingPolynomial_comp e.toEquiv v i j
  simp_rw [hr]
  have h := (e.toEquiv.prodCongr e.toEquiv).sum_comp (fun p : κ × κ =>
    if p.1 < p.2 then
      MvPolynomial.C (wedge v p.1 p.2 a b) * remainingPolynomial v p.1 p.2 else 0)
  simpa only [Equiv.prodCongr_apply, OrderIso.coe_toEquiv, Prod.map_fst, Prod.map_snd,
    OrderIso.lt_iff_lt, wedge] using h

def contiguousRows {n : ℕ} (v : Fin n → C → R) (L : ℕ) : Fin (n * L) → C → R :=
  fun i => repeatRows v L (monoEquivOfFin (Fin n ×ₗ Fin L) (by simp) i)

theorem formsProduct_contiguousRows {n : ℕ} (v : Fin n → C → R) (L : ℕ) :
    formsProduct (contiguousRows v L) = (formsProduct v)^L := by
  exact (formsProduct_comp
    (monoEquivOfFin (Fin n ×ₗ Fin L) (by simp : Fintype.card (Fin n ×ₗ Fin L) = n * L)).toEquiv
    (repeatRows v L)).trans (formsProduct_repeat v L)

theorem wedgePolynomial_contiguousRows {n : ℕ} (v : Fin n → C → R)
    {L : ℕ} (hL : 0 < L) (a b : C) :
    wedgePolynomial (contiguousRows v L) a b =
      MvPolynomial.C ((L : R)^2) * (formsProduct v)^(L-1) * wedgePolynomial v a b := by
  unfold contiguousRows
  rw [wedgePolynomial_orderIso, wedgePolynomial_repeat v hL]

/-- The repeated endpoint identity is for the actual Fin-indexed q-permanent,
with the lexicographic block order transported by an increasing bijection. -/
theorem real_contiguous_endpoint {n L : ℕ} (v : Fin n → C → ℝ) (hL : 0 < L) :
    2 * (qPolynomial (gram (contiguousRows v L))).derivative.eval 1 =
      ((n * L).choose 2 : ℝ) * fischerNormSq ((formsProduct v)^L) -
        (L : ℝ)^4 * ∑ c ∈ originalPairs (ι := C),
          fischerNormSq ((formsProduct v)^(L-1) * wedgePolynomial v c.1 c.2) := by
  rw [real_endpoint_fischer, formsProduct_contiguousRows]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [wedgePolynomial_contiguousRows v hL]
  simp only [mul_assoc, fischerNormSq, fischerPair_C_mul_left, fischerPair_C_mul_right]
  ring

end
end BapatFiniteRank
