import ContinuumGeometric.GeometryChain
import ContinuumGeometric.ClosedProjection

/-!
Exact countable compact-parameter reduction for EVERY nonzero affine coefficient
and EVERY real geometric ratio in (0,1). Negative coefficients use reflection;
no coefficients, translations, ratios or tails are discretized.
-/
namespace ContinuumGeometric

/-- All positive magnitudes, including arbitrarily small ones, have an integer dyadic shift. -/
theorem positive_dyadic_coefficient_cover (a : ℝ) (ha : 0 < a) :
    ∃ k : ℤ, ∃ t : ℝ, 1 ≤ t ∧ t < 2 ∧ a = t * (2 : ℝ) ^ k := by
  let k : ℤ := Int.floor (Real.logb 2 a)
  have hk : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hlow : (2 : ℝ) ^ k ≤ a := by
    rw [← Real.rpow_intCast]
    calc
      (2 : ℝ) ^ (k : ℝ) ≤ (2 : ℝ) ^ Real.logb 2 a :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)
      _ = a := Real.rpow_logb (by norm_num) (by norm_num) ha
  have hhigh : a < 2 * (2 : ℝ) ^ k := by
    calc
      a = (2 : ℝ) ^ Real.logb 2 a :=
        (Real.rpow_logb (by norm_num) (by norm_num) ha).symm
      _ < (2 : ℝ) ^ ((k : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Int.lt_floor_add_one _)
      _ = 2 * (2 : ℝ) ^ k := by
        rw [Real.rpow_add (by norm_num), Real.rpow_intCast, Real.rpow_one, mul_comm]
  refine ⟨k, a / (2 : ℝ) ^ k, (le_div_iff₀ hk).2 ?_, (div_lt_iff₀ hk).2 hhigh, ?_⟩
  · simpa using hlow
  · exact (div_mul_cancel₀ a hk.ne').symm

/-- The only extra index for signed coefficients is a two-point sign set. -/
theorem signed_dyadic_coefficient_cover (a : ℝ) (ha : a ≠ 0) :
    ∃ positive : Bool, ∃ k : ℤ, ∃ t : ℝ,
      1 ≤ t ∧ t < 2 ∧ a = (if positive then 1 else -1) * t * (2 : ℝ) ^ k := by
  by_cases hp : 0 < a
  · obtain ⟨k, t, ht, ht', heq⟩ := positive_dyadic_coefficient_cover a hp
    exact ⟨true, k, t, ht, ht', by simpa using heq⟩
  · have hn : 0 < -a := by have := lt_of_le_of_ne (le_of_not_gt hp) ha; linarith
    obtain ⟨k, t, ht, ht', heq⟩ := positive_dyadic_coefficient_cover (-a) hn
    exact ⟨false, k, t, ht, ht', by simp only [Bool.false_eq_true, ↓reduceIte]; linarith⟩

/-- Every real affine geometric progression is exactly a compact power point or its reflection. -/
theorem affine_geometric_compact_power_cover (a b q : ℝ) (ha : a ≠ 0)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ positive : Bool, ∃ k : ℤ,
      ∃ p : PowerParams (1 / (K : ℝ)) K, ∀ n : ℕ,
        a * q ^ n + b =
          if positive then powerPoint (dyadic n) ((2 : ℝ) ^ k) (b, p)
          else -powerPoint (dyadic n) ((2 : ℝ) ^ k) (-b, p) := by
  obtain ⟨s, hs, hq⟩ := geometric_parameter q hq₀ hq₁
  obtain ⟨K, hK, hsK⟩ := exists_compact_exponent_range s hs
  obtain ⟨positive, k, t, ht, ht', haeq⟩ := signed_dyadic_coefficient_cover a ha
  let p : PowerParams (1 / (K : ℝ)) K :=
    (⟨s, hsK⟩, ⟨t, ⟨ht, ht'.le⟩⟩)
  refine ⟨K, hK, positive, k, p, ?_⟩
  intro n
  rw [hq n, haeq]
  cases positive <;> simp [powerPoint, p]
  ring

end ContinuumGeometric
