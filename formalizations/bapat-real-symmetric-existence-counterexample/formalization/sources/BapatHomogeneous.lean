import BapatOrderedRepetition
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

variable {ι C R : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype C] [LinearOrder C] [CommRing R]

theorem linearForm_isHomogeneous (v : C → R) :
    (linearForm v).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro c hc
  apply MvPolynomial.isHomogeneous_monomial
  exact Finsupp.degree_single c 1

theorem formsProduct_isHomogeneous (v : ι → C → R) :
    (formsProduct v).IsHomogeneous (Fintype.card ι) := by
  simpa [formsProduct] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => linearForm (v i)) (fun _ => 1)
    (fun i _ => linearForm_isHomogeneous (v i))

theorem remainingPolynomial_isHomogeneous (v : ι → C → R) {i j : ι} (hij : i ≠ j) :
    (remainingPolynomial v i j).IsHomogeneous (Fintype.card ι - 2) := by
  simpa only [remainingPolynomial, twoPointComplement_card hij] using
    formsProduct_isHomogeneous (fun x : TwoPointComplement i j => v x.val)

theorem wedgePolynomial_isHomogeneous (v : ι → C → R) (a b : C) :
    (wedgePolynomial v a b).IsHomogeneous (Fintype.card ι - 2) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro p hp
  exact (remainingPolynomial_isHomogeneous v
    (ne_of_lt (Finset.mem_filter.mp hp).2)).C_mul _

theorem power_wedge_isHomogeneous (v : ι → C → R) (hn : 2 ≤ Fintype.card ι)
    {L : ℕ} (hL : 0 < L) (a b : C) :
    ((formsProduct v)^(L-1) * wedgePolynomial v a b).IsHomogeneous
      (Fintype.card ι * L - 2) := by
  have h := ((formsProduct_isHomogeneous v).pow (L-1)).mul
    (wedgePolynomial_isHomogeneous v a b)
  have he : Fintype.card ι * (L-1) + (Fintype.card ι - 2) =
      Fintype.card ι * L - 2 := by
    have ht : Fintype.card ι * (L-1) + Fintype.card ι = Fintype.card ι * L := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hL]
    omega
  simpa only [he] using h

end BapatFiniteRank
