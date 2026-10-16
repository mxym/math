import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace SymmetricSupport

noncomputable section

def phaseRoot (L : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / L)

theorem phaseRoot_primitive (L : ℕ) (hL : 0 < L) :
    IsPrimitiveRoot (phaseRoot L) L :=
  Complex.isPrimitiveRoot_exp L (Nat.ne_of_gt hL)

theorem sum_root_powers_zero {L : ℕ} (q : ℂ) (hq : q ^ L = 1) (hne : q ≠ 1) :
    ∑ j : Fin L, q ^ j.val = 0 := by
  have h := geom_sum_mul q L
  rw [hq, sub_self] at h
  have hz : (∑ j ∈ Finset.range L, q ^ j) = 0 :=
    (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  simpa only [← Fin.sum_univ_eq_sum_range] using hz

theorem phase_correlation {L : ℕ} (hL : 0 < L) (a b : ℕ) (ha : a < L) (hb : b < L) :
    (∑ j : Fin L,
      ((phaseRoot L ^ a) / (phaseRoot L ^ b)) ^ j.val) =
      if a = b then (L : ℂ) else 0 := by
  classical
  have hp := phaseRoot_primitive L hL
  have hζ : phaseRoot L ≠ 0 := hp.ne_zero (Nat.ne_of_gt hL)
  by_cases hab : a = b
  · subst b
    simp [pow_ne_zero _ hζ]
  · rw [ite_eq_right hab]
    apply sum_root_powers_zero
    · rw [div_pow, ← pow_mul, ← pow_mul, mul_comm a L, mul_comm b L,
        pow_mul, pow_mul, hp.pow_eq_one]
      simp
    · intro hc
      exact hab (hp.pow_inj ha hb ((div_eq_one_iff_eq (pow_ne_zero _ hζ)).mp hc))

theorem phase_correlation_star {L : ℕ} (hL : 0 < L)
    (a b : ℕ) (ha : a < L) (hb : b < L) :
    (∑ j : Fin L, (phaseRoot L ^ j.val) ^ a * star ((phaseRoot L ^ j.val) ^ b)) =
      if a = b then (L : ℂ) else 0 := by
  have hnorm : ‖phaseRoot L‖ = 1 := (phaseRoot_primitive L hL).norm'_eq_one (Nat.ne_of_gt hL)
  have ht : ∀ j : Fin L,
      (phaseRoot L ^ j.val) ^ a * star ((phaseRoot L ^ j.val) ^ b) =
        ((phaseRoot L ^ a) / (phaseRoot L ^ b)) ^ j.val := by
    intro j
    have hc : star ((phaseRoot L ^ j.val) ^ b) = ((phaseRoot L ^ j.val) ^ b)⁻¹ :=
      (Complex.inv_eq_conj (by simp [norm_pow, hnorm])).symm
    rw [hc]
    rw [div_pow, div_eq_mul_inv]
    congr 1
    · rw [← pow_mul, ← pow_mul, mul_comm j.val a]
    · rw [← pow_mul, ← pow_mul, mul_comm j.val b]
  simp_rw [ht]
  exact phase_correlation hL a b ha hb

end
end SymmetricSupport
