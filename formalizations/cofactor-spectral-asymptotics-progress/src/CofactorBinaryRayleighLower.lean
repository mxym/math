import CofactorNormalizedRankTwo
import CofactorRootRingMoments
import CofactorExtremaUpper

/-! Actual complex and real test vectors for the normalized binary Gram matrix.
The denominator estimate is an explicit remaining finite-product interface. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

theorem normalizedBinaryGram_test_lower {n : ℕ} (z w : Fin (n+1) → ℂ)
    (T S : ℝ) (hT : 0 < T) (hS : 0 < S)
    (hw : vectorNormSq w = S)
    (hm : Complex.normSq (∑ i, star (w i)*z i) = S^2)
    (hp : (normalizedBinaryGram z).permanent.re ≤
      ((n+1).factorial : ℝ)*(binaryGamma z)^2*T) :
    S / ((n+1 : ℝ)*T) ≤ cofactorRayleighRatio (normalizedBinaryGram z) w := by
  have hmarked := normalizedBinaryGram_marked_lower z w
  simp only [Fintype.card_fin,Nat.add_sub_cancel,hm] at hmarked
  have hN : (0 : ℝ) < n+1 := by positivity
  have hden := mul_pos (normalizedBinaryGram_permanent_pos z) hS
  have hfac : ((n+1).factorial : ℝ) = (n+1 : ℝ)*(n.factorial : ℝ) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  unfold cofactorRayleighRatio
  rw [hw]
  apply (div_le_div_iff₀ (mul_pos hN hT) hden).2
  calc
    S * ((normalizedBinaryGram z).permanent.re*S) =
        (normalizedBinaryGram z).permanent.re*S^2 := by ring
    _ ≤ (((n+1).factorial : ℝ)*(binaryGamma z)^2*T)*S^2 :=
      mul_le_mul_of_nonneg_right hp (sq_nonneg S)
    _ = ((n.factorial : ℝ)*(binaryGamma z)^2*S^2)*((n+1 : ℝ)*T) := by
      rw [hfac]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmarked (mul_pos hN hT).le

theorem vectorNormSq_self_test {n : ℕ} (z : Fin n → ℂ) :
    Complex.normSq (∑ i, star (z i)*z i) = (vectorNormSq z)^2 := by
  have he : (∑ i, star (z i)*z i) = (vectorNormSq z : ℂ) := by
    simp [vectorNormSq,Complex.normSq_eq_conj_mul_self]
  rw [he,Complex.normSq_ofReal]
  ring

theorem normalizedBinaryGram_complex_test_lower {n : ℕ} (z : Fin (n+1) → ℂ)
    (T : ℝ) (hT : 0 < T) (hz : 0 < vectorNormSq z)
    (hp : (normalizedBinaryGram z).permanent.re ≤
      ((n+1).factorial : ℝ)*(binaryGamma z)^2*T) :
    vectorNormSq z / ((n+1 : ℝ)*T) ≤
      cofactorRayleighRatio (normalizedBinaryGram z) z :=
  normalizedBinaryGram_test_lower z z T (vectorNormSq z) hT hz rfl
    (vectorNormSq_self_test z) hp

theorem imaginary_test_normSq {n : ℕ} (z : Fin n → ℂ) (hz : ∑ i, z i^2 = 0) :
    Complex.normSq (∑ i, star ((z i).im : ℂ)*z i) =
      (vectorNormSq (fun i => ((z i).im : ℂ)))^2 := by
  simp only [Complex.star_def,Complex.conj_ofReal]
  rw [imaginary_test_sum_of_square_sum_zero z hz,Complex.normSq_mul,
    Complex.normSq_I,one_mul,Complex.normSq_ofReal]
  simp only [vectorNormSq,Complex.normSq_ofReal,pow_two]

theorem normalizedBinaryGram_real_test_lower {n : ℕ} (z : Fin (n+1) → ℂ)
    (T : ℝ) (hT : 0 < T) (hz : ∑ i, z i^2 = 0)
    (hi : 0 < vectorNormSq (fun i => ((z i).im : ℂ)))
    (hp : (normalizedBinaryGram z).permanent.re ≤
      ((n+1).factorial : ℝ)*(binaryGamma z)^2*T) :
    vectorNormSq (fun i => ((z i).im : ℂ)) / ((n+1 : ℝ)*T) ≤
      cofactorRayleighRatio (normalizedBinaryGram z) (fun i => ((z i).im : ℂ)) :=
  normalizedBinaryGram_test_lower z (fun i => ((z i).im : ℂ)) T
    (vectorNormSq (fun i => ((z i).im : ℂ))) hT hi rfl
    (imaginary_test_normSq z hz) hp

end
end CofactorSpectral
