import ContinuumGeometric.EntropySchedule
import ContinuumGeometric.LocalSignatures

/-!
Scalar choices preceding the output schedule: branching, default-depth and
stable-center gap budgets are fixed before U or the finite random table outcome.
No independence or blocker existence is asserted by these scalar lemmas.
-/
namespace ContinuumGeometric

open Filter Topology

theorem exists_branching_decay (p η : ℝ) (hp : 0 < p) (hη : 0 < η) :
    ∃ M : ℕ, 2 ≤ M ∧ 12 ≤ p * η * ((M : ℝ) - 1) ∧
      0 < p * η * ((M : ℝ) - 1) / 2 - 4 * Real.log 2 := by
  have hprod : 0 < p * η := mul_pos hp hη
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 : ℝ) (12 / (p * η) + 1))
  have hM₂ : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMlarge : 12 / (p * η) < (M : ℝ) - 1 := by
    have := (le_max_right _ _).trans_lt hM
    linarith
  have hdecay : 12 < p * η * ((M : ℝ) - 1) := by
    simpa [mul_comm] using (div_lt_iff₀ hprod).1 hMlarge
  have hlog : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  refine ⟨M, ?_, hdecay.le, ?_⟩
  · exact_mod_cast hM₂.le
  · linarith

/-- The probability of avoiding every default can be made small with a fixed finite depth. -/
theorem exists_default_depth_budget (M : ℕ) (hM : 2 ≤ M) (p : ℝ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧
      (1 - (2 : ℝ) ^ (1 - (M : ℝ))) ^ d < p := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 0 < (2 : ℝ) ^ (1 - (M : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hb : (2 : ℝ) ^ (1 - (M : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq₀ : 0 < 1 - (2 : ℝ) ^ (1 - (M : ℝ)) := by linarith
  have hq₁ : 1 - (2 : ℝ) ^ (1 - (M : ℝ)) < 1 := by linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁
  obtain ⟨d, hprob, hd⟩ := ((ht.eventually_lt_const hp).and
    (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨d, hd, hprob⟩

theorem half_selector_default_probability_eq (M : ℕ) (hM : 1 ≤ M) :
    (1 / 2 : ℝ) ^ (M - 1) = (2 : ℝ) ^ (1 - (M : ℝ)) := by
  calc
    _ = (2 : ℝ) ^ (-((M - 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      simp [one_div, inv_pow]
    _ = _ := by congr 1; rw [Nat.cast_sub hM]; push_cast; ring

theorem dyadic_integer_gap_rpow (g : ℕ) :
    (2 : ℝ) ^ ((3 : ℤ) - (g : ℤ)) = (2 : ℝ) ^ (3 - (g : ℝ)) := by
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem stable_gap_cost_eq (g : ℕ) :
    (2 : ℝ) ^ (3 - (g : ℝ)) = 8 * (1 / 2 : ℝ) ^ g := by
  have h := (dyadic_shifted_offset g 1 1 3).symm
  norm_num [dyadic, Real.rpow_one] at h ⊢
  exact h

/-- Every fixed finite template has an arbitrarily late small stable-center gap cost. -/
theorem exists_stable_gap_budget (edges : ℕ) (p : ℝ) (hp : 0 < p) (gmin : ℕ) :
    ∃ g : ℕ, gmin ≤ g ∧ (edges : ℝ) * (2 : ℝ) ^ (3 - (g : ℝ)) < p := by
  have ht : Tendsto (fun g : ℕ => (edges : ℝ) * 8 * (1 / 2 : ℝ) ^ g)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        ((edges : ℝ) * 8)
  obtain ⟨g, hcost, hlate⟩ := ((ht.eventually_lt_const hp).and
    (eventually_ge_atTop gmin)).exists
  refine ⟨g, hlate, ?_⟩
  rw [stable_gap_cost_eq]
  simpa [mul_assoc] using hcost

end ContinuumGeometric
