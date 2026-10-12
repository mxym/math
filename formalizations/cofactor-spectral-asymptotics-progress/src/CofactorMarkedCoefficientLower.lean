import CofactorGramPSD

/-! Keeping one actual marked Fock coefficient gives a Rayleigh lower bound in every rank. -/
set_option autoImplicit false
open scoped BigOperators
open BapatFiniteRank
namespace CofactorSpectral
noncomputable section
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem fockNormSq_coefficient_lower (p : MvPolynomial C ℂ) (α : C →₀ ℕ) :
    (multiFactorial α : ℝ) * Complex.normSq (p.coeff α) ≤ fockNormSq p := by
  classical
  by_cases hα : α ∈ p.support
  · unfold fockNormSq
    rw [MvPolynomial.sum_def]
    exact Finset.single_le_sum (fun β _ =>
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) hα
  · have hz : p.coeff α = 0 := by simpa using hα
    simpa only [hz,Complex.normSq_zero,mul_zero] using fockNormSq_nonneg p

theorem marked_coefficient_quadratic_lower (v : V → C → ℂ) (w : V → ℂ)
    (c : C) (α : C →₀ ℕ) :
    (multiFactorial α : ℝ) * Complex.normSq ((markedSum v w c).coeff α) ≤
      (∑ i,∑ j,star (w i) * compound (complexGram v) i j * w j).re := by
  rw [compound_quadratic_complexGram,Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact (fockNormSq_coefficient_lower (markedSum v w c) α).trans
    (Finset.single_le_sum (fun d _ => fockNormSq_nonneg (markedSum v w d))
      (Finset.mem_univ c))

end
end CofactorSpectral
