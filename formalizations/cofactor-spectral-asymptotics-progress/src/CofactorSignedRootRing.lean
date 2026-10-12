import CofactorRootRingMoments
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Existence of actual signed rings with prescribed squared radius and exact homogeneous product. -/
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
namespace CofactorSpectral
noncomputable section

def signedRingCoefficient (ε : Bool) (R : ℝ) (d : ℕ) : ℝ :=
  (if ε then -1 else 1) * R^d

theorem exists_signed_root_ring (d : ℕ) (hd : 2 ≤ d) (R : ℝ) (hR : 0 < R) (ε : Bool) :
    ∃ z : Fin (2*d) → ℂ,
      (∀ i, Complex.normSq (z i) = R) ∧
      (∑ i, z i) = 0 ∧ (∑ i, z i^2) = 0 ∧
      (∑ i, (z i).im^2) = (d : ℝ)*R ∧
      (∏ i, (X (0 : Fin 2)+C (z i)*X (1 : Fin 2))) =
        X (0 : Fin 2)^(2*d) + C (signedRingCoefficient ε R d : ℂ)*X (1 : Fin 2)^(2*d) := by
  have hn : 0 < 2*d := by omega
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(signedRingCoefficient ε R d : ℂ)) hn
  have ht : ‖-(signedRingCoefficient ε R d : ℂ)‖ = R^d := by
    cases ε <;> simp [signedRingCoefficient,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hR]
  have hpow : ‖a‖^(2*d) = R^d := by
    rw [← norm_pow,ha]
    exact ht
  have hsquare : Complex.normSq a = R := by
    apply (pow_left_inj₀ (Complex.normSq_nonneg a) hR.le (by omega : d ≠ 0)).mp
    rw [Complex.normSq_eq_norm_sq,← pow_mul]
    exact hpow
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/((2*d : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (2*d) := Complex.isPrimitiveRoot_exp (2*d) (by omega)
  refine ⟨ringSlope ζ a,?_,ringSlope_sum _ (by omega) ζ a hζ,
    ringSlope_square_sum _ (by omega) ζ a hζ,?_,?_⟩
  · intro i
    rw [ringSlope_normSq (2*d) (by omega) ζ a hζ i,hsquare]
  · rw [ringSlope_imaginary_square_sum (2*d) (by omega) ζ a hζ,hsquare]
    push_cast
    ring
  · rw [ring_homogeneous_product (2*d) hn ζ a hζ,ha]
    simp only [map_neg]
    ring

end
end CofactorSpectral
