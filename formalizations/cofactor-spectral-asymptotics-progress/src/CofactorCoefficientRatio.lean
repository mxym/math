import CofactorBinaryPermanent

/-! Exact binomial denominator in the normalized permanent coefficient ratio. -/
set_option autoImplicit false
open scoped BigOperators
open BapatFischer
namespace CofactorSpectral
noncomputable section

def binaryCoefficientRatio (n : ℕ) (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), Complex.normSq (p.coeff k)/(n.choose k : ℝ)

theorem fischerNormSq_eq_factorial_coefficientRatio (n : ℕ) (p : Polynomial ℂ) :
    fischerNormSq n p = (n.factorial : ℝ)*binaryCoefficientRatio n p := by
  unfold fischerNormSq binaryCoefficientRatio
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  have hc : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos hkn)
  have hf : (n.choose k : ℝ)*(k.factorial : ℝ)*((n-k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  simp only [Nat.cast_mul]
  rw [← mul_div_assoc]
  apply (eq_div_iff hc).2
  calc
    _ = ((n.choose k : ℝ)*(k.factorial : ℝ)*((n-k).factorial : ℝ))*
        Complex.normSq (p.coeff k) := by ring
    _ = _ := by rw [hf]

theorem binaryCoefficientRatio_nonneg (n : ℕ) (p : Polynomial ℂ) :
    0 ≤ binaryCoefficientRatio n p :=
  Finset.sum_nonneg fun k _ => div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem binaryCoefficientRatio_ge_one (n : ℕ) (p : Polynomial ℂ) (hp : p.coeff 0 = 1) :
    1 ≤ binaryCoefficientRatio n p := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.range (n+1)) =>
      div_nonneg (Complex.normSq_nonneg (p.coeff k)) (Nat.cast_nonneg (n.choose k)))
    (by simp : 0 ∈ Finset.range (n+1))
  simpa only [hp,Complex.normSq_one,Nat.choose_zero_right,Nat.cast_one,div_one,
    binaryCoefficientRatio] using h

theorem normalizedBinaryGram_permanent_ratio {V : Type*} [Fintype V] [DecidableEq V]
    (z : V → ℂ) :
    (normalizedBinaryGram z).permanent.re =
      ((Fintype.card V).factorial : ℝ)*(binaryGamma z)^2*
        binaryCoefficientRatio (Fintype.card V) (slopePolynomial z) := by
  rw [normalizedBinaryGram_permanent_formula,fischerNormSq_eq_factorial_coefficientRatio]
  ring

end
end CofactorSpectral
