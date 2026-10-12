import PositiveDefiniteViolation

namespace BapatBounds

theorem dimension_at_least_three_bounds (n : ℕ) (hn : 3 ≤ n) (R : ℝ) (hR : 0 ≤ R) :
    1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1) ∧
    1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n := by
  have hN3 : 3 ≤ n.choose 2 := by
    calc
      3 = Nat.choose 3 2 := by decide
      _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn
  have hN : (1 : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast (by omega : 1 ≤ n.choose 2)
  have hNm : (1 : ℝ) ≤ ((n.choose 2 - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n.choose 2 - 1)
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hd : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hp : ∀ m : ℕ, (1 : ℝ) ≤ (R + 1) ^ m := fun _m => one_le_pow₀ (by linarith)
  have hm (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
    have hh := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ a)
    simpa using hh
  exact ⟨hm _ _ (hm _ _ (hm _ _ hN hf) hd) (hp _),
    hm _ _ (hm _ _ (hm _ _ hN hNm) hf) (hp _)⟩

end BapatBounds
