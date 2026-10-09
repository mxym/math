import CofactorSignOrthogonality

/-! Exact square averaging of finite sign expansions; equal degree sums do not create cross terms. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def signCombination (a : Finset V → ℝ) (ε : V → Bool) : ℝ :=
  ∑ s : Finset V, a s * signCharacter ε s

theorem signCombination_square_sum (a : Finset V → ℝ) :
    (∑ ε : V → Bool, signCombination a ε ^ 2) =
      (2 : ℝ)^Fintype.card V * ∑ s : Finset V, a s ^ 2 := by
  classical
  calc
    _ = ∑ ε : V → Bool, ∑ s : Finset V, ∑ t : Finset V,
        (a s*a t) * (signCharacter ε s * signCharacter ε t) := by
      simp only [signCombination,pow_two,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ε _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ s : Finset V, ∑ t : Finset V,
        (a s*a t) * (∑ ε : V → Bool, signCharacter ε s * signCharacter ε t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [signCharacter_orthogonality]
      simp only [mul_ite,mul_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
      ring

theorem signCombination_square_average (a : Finset V → ℝ) :
    (∑ ε : V → Bool, signCombination a ε ^ 2) / (2 : ℝ)^Fintype.card V =
      ∑ s : Finset V, a s ^ 2 := by
  rw [signCombination_square_sum]
  field_simp

theorem finite_average_has_small_choice {T : Type*} [Fintype T] [Nonempty T]
    (f : T → ℝ) (B : ℝ) (h : (∑ t, f t)/(Fintype.card T : ℝ) ≤ B) :
    ∃ t, f t ≤ B := by
  classical
  by_contra! hn
  have hc : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (Fintype.card T : ℝ)*B < ∑ t, f t := by
    calc
      _ = ∑ _t : T, B := by simp
      _ < _ := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun t _ => hn t)
  have hm := (div_le_iff₀ hc).mp h
  nlinarith

end
end CofactorSpectral
