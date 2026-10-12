import APPTReview.PlateauApproximation

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The scaled purity of a two-level projection plateau, written as a real
quantity so that its elementary finite-rank optimization can be stated
independently of a chosen projection. -/
noncomputable def plateauScaledPurity (m n k : ℕ) : ℝ :=
  ((m : ℝ) * n) *
    (((m : ℝ) * n * ((m : ℝ) - 1)^2 + 4 * (m : ℝ) * k) /
      (plateauDenominator m n k)^2)

/-- Every projection plateau lies below the continuous two-level value.  This
is an exact consequence of the square-deficit identity, not an asymptotic
estimate. -/
theorem plateauScaledPurity_le_continuous {m n k : ℕ}
    (hm : 2 ≤ m) (hn : 0 < n) :
    plateauScaledPurity m n k ≤ (m : ℝ)^2 / ((m : ℝ)^2 - 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < (m : ℝ)^2 - 1 := by nlinarith
  have hZ : (0 : ℝ) < (m : ℝ) * n * ((m : ℝ) - 1) + 2 * (k : ℝ) := by
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  have hid := plateau_rounding_identity
    (m : ℝ) (n : ℝ) (k : ℝ) (ne_of_gt hbase)
    (ne_of_gt hZ)
  have hq : plateauScaledPurity m n k =
      ((m : ℝ)^2 / ((m : ℝ)^2 - 1)) -
        ((m : ℝ)^2 / ((m : ℝ)^2 - 1)) *
          ((2 : ℝ) * k - ((m : ℝ) - 1) * n)^2 /
            ((m : ℝ) * n * ((m : ℝ) - 1) + 2 * (k : ℝ))^2 := by
    dsimp [plateauScaledPurity, plateauDenominator]
    rw [← hid]
    ring
  rw [hq]
  have hfrac : 0 ≤
      ((m : ℝ)^2 / ((m : ℝ)^2 - 1)) *
        ((2 : ℝ) * k - ((m : ℝ) - 1) * n)^2 /
          ((m : ℝ) * n * ((m : ℝ) - 1) + 2 * (k : ℝ))^2 := by
    positivity
  linarith

/-- If the target rank is integral (the even-parity case), the rounded
projection plateau attains the continuous two-level value and is therefore an
exact maximizer among all projection plateaus. -/
theorem plateauScaledPurity_even_rank_max
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (hpar : Even ((m - 1) * n)) :
    let k₀ := ((m - 1) * n) / 2
    plateauScaledPurity m n k₀ = (m : ℝ)^2 / ((m : ℝ)^2 - 1) ∧
      ∀ k : ℕ, plateauScaledPurity m n k ≤ plateauScaledPurity m n k₀ := by
  dsimp
  obtain ⟨r, hr⟩ := hpar
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < (m : ℝ)^2 - 1 := by nlinarith
  have hdiv : ((m - 1) * n) / 2 = r := by
    rw [hr]
    omega
  have htwoNat : 2 * (((m - 1) * n) / 2) = (m - 1) * n := by
    rw [hdiv, hr]
    omega
  have htwo : (2 : ℝ) * ((((m - 1) * n) / 2 : ℕ) : ℝ) =
      ((m : ℝ) - 1) * n := by
    calc
      _ = ((2 * (((m - 1) * n) / 2 : ℕ) : ℕ) : ℝ) := by norm_num
      _ = (((m - 1) * n : ℕ) : ℝ) := by rw [htwoNat]
      _ = ((m : ℝ) - 1) * n := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hZ : (0 : ℝ) < (m : ℝ) * n * ((m : ℝ) - 1) +
      2 * ((((m - 1) * n) / 2 : ℕ) : ℝ) := by
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    positivity
  have hid := plateau_rounding_identity
    (m : ℝ) (n : ℝ) ((((m - 1) * n) / 2 : ℕ) : ℝ)
    (ne_of_gt hbase) (ne_of_gt hZ)
  have hq0 : plateauScaledPurity m n (((m - 1) * n) / 2) =
      (m : ℝ)^2 / ((m : ℝ)^2 - 1) := by
    have hz : ((2 : ℝ) * ((((m - 1) * n) / 2 : ℕ) : ℝ) -
        ((m : ℝ) - 1) * n) = 0 := by linarith [htwo]
    have hid0 := hid
    rw [hz] at hid0
    simp at hid0
    dsimp [plateauScaledPurity, plateauDenominator]
    linarith
  refine ⟨hq0, ?_⟩
  intro k
  exact (plateauScaledPurity_le_continuous hm hn).trans_eq hq0.symm

end APPTReview
