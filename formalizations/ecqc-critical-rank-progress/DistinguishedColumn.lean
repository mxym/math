import Mathlib

namespace ECQCCriticalRank
noncomputable section

/-- Diagonal rigidity from the distinguished first column. The equation is the
entrywise expansion of `D * F = F * B` for a monomial matrix `B`. -/
theorem diagonal_rigidity_of_distinguished_column
    {ι : Type*} (F : Matrix ι ι ℂ) (zero : ι)
    (d phase : ι → ℂ) (σ : ι ≃ ι)
    (hd : ∀ i, ‖d i‖ = 1) (hphase : ∀ j, ‖phase j‖ = 1)
    (hrel : ∀ i j, d i * F i j = F i (σ j) * phase j)
    (hunique : ∀ j, ‖F zero zero‖ = ‖F zero j‖ → j = zero)
    (hnonzero : ∀ i, F i zero ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, d i = c := by
  have hσ : σ zero = zero := by
    apply hunique
    have h := congrArg norm (hrel zero zero)
    simpa only [norm_mul, hd, hphase, one_mul, mul_one] using h
  refine ⟨phase zero, hphase zero, ?_⟩
  intro i
  have h := hrel i zero
  rw [hσ, mul_comm (F i zero)] at h
  exact mul_right_cancel₀ (hnonzero i) h

#print axioms diagonal_rigidity_of_distinguished_column
end
end ECQCCriticalRank
