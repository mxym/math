import Entry002.WeakSupplyInterfaces

/-! Unconditional finite dyadic estimates for a set of actual primes. -/

namespace Entry002

open scoped BigOperators Classical

theorem supply_dyadicPrimeBatch_log_weight_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (j : ℕ) :
    (∑ p ∈ dyadicPrimeBatch P j, Real.log (p : ℝ)) ≤
      Real.log 4 * (2 : ℝ) ^ (j + 1) := by
  apply prime_log_mass_le_theta _ (by positivity)
  intro p hp
  obtain ⟨hpP, _, hhi⟩ := (mem_dyadicPrimeBatch P j p).mp hp
  exact ⟨hP p hpP, hhi⟩

/-- The actual Chebyshev upper bound gives a uniform harmonic-sized batch cap. -/
theorem supply_dyadicPrimeBatch_card_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {j : ℕ} (hj : 1 ≤ j) :
    ((dyadicPrimeBatch P j).card : ℝ) ≤ 8 * (2 : ℝ) ^ j / ((j : ℝ) + 1) := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmass : ((dyadicPrimeBatch P j).card : ℝ) * Real.log ((2 : ℝ) ^ j) ≤
      ∑ p ∈ dyadicPrimeBatch P j, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ dyadicPrimeBatch P j, Real.log ((2 : ℝ) ^ j) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by positivity) ((mem_dyadicPrimeBatch P j p).mp hp).2.1
  have hcap := hmass.trans (supply_dyadicPrimeBatch_log_weight_le P hP j)
  rw [Real.log_pow, show Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
    pow_succ] at hcap
  have hcap' : ((dyadicPrimeBatch P j).card : ℝ) * (j : ℝ) ≤ 4 * (2 : ℝ) ^ j := by
    apply (mul_le_mul_iff_right₀ hl).mp
    convert hcap using 1 <;> ring
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
  nlinarith [show (0 : ℝ) ≤ (dyadicPrimeBatch P j).card by positivity]

/-- The real norm power over a dyadic bin factors into its size and discount. -/
theorem supply_dyadic_rpow_discount (j : ℕ) (ε : ℝ) :
    1 / ((2 : ℝ) ^ j) ^ (1 + ε) =
      (1 / (2 : ℝ) ^ j) * ((2 : ℝ) ^ (-ε)) ^ j := by
  have hq : ((2 : ℝ) ^ (-ε)) ^ j = ((2 : ℝ) ^ ((j : ℝ) * ε))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (-ε) * (j : ℝ) = -((j : ℝ) * ε) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), hq]
  simp [div_eq_mul_inv, mul_comm]

theorem supply_dyadicPrimeBatch_dirichlet_le (P : Set ℕ) (j : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (∑ p ∈ dyadicPrimeBatch P j, 1 / (p : ℝ) ^ (1 + ε)) ≤
      ((dyadicPrimeBatch P j).card / (2 : ℝ) ^ j) * ((2 : ℝ) ^ (-ε)) ^ j := by
  calc
    _ ≤ ∑ _p ∈ dyadicPrimeBatch P j, 1 / ((2 : ℝ) ^ j) ^ (1 + ε) := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le (by positivity)
      exact Real.rpow_le_rpow (by positivity)
        ((mem_dyadicPrimeBatch P j p).mp hp).2.1 (by linarith)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, supply_dyadic_rpow_discount]
      ring

end Entry002
