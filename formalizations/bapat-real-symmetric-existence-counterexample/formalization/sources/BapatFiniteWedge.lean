import BapatMarkedInversions

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

variable {C R : Type*} [Fintype C] [LinearOrder C] [CommRing R]

/-- Pair opposite off-diagonal terms using the actual coordinate order. -/
theorem sum_pairing (f : C → C → R) (hdiag : ∀ c, f c c = 0) :
    (∑ a, ∑ b, f a b) =
      ∑ p ∈ originalPairs (ι := C), (f p.1 p.2 + f p.2 p.1) := by
  classical
  have hs : (∑ p : C × C, if p.1 < p.2 then f p.2 p.1 else 0) =
      ∑ p : C × C, if p.2 < p.1 then f p.1 p.2 else 0 := by
    exact Fintype.sum_equiv (Equiv.prodComm C C) _ _ (fun _ => rfl)
  rw [Finset.sum_add_distrib]
  simp only [originalPairs, Finset.sum_filter]
  rw [hs, ← Finset.sum_add_distrib,
    ← Fintype.sum_prod_type (fun p : C × C => f p.1 p.2)]
  apply Finset.sum_congr rfl
  intro p hp
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · simp [h, not_lt_of_gt h]
  · simp [h, hdiag]
  · simp [h, not_lt_of_gt h]

/-- Finite-coordinate two-row Cauchy--Binet, with each wedge coordinate once. -/
theorem dot_minor_eq_wedges (x y z t : C → R) :
    (∑ a, x a * z a) * (∑ a, y a * t a) -
      (∑ a, x a * t a) * (∑ a, y a * z a) =
    ∑ p ∈ originalPairs (ι := C),
      (x p.1 * y p.2 - x p.2 * y p.1) *
      (z p.1 * t p.2 - z p.2 * t p.1) := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  rw [sum_pairing (fun a b => x a * z a * (y b * t b) - x a * t a * (y b * z b))
    (fun a => by ring)]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end BapatFiniteRank
