import Entry002.WeakSupplyGoodBinUpper
import Entry002.WeakSupplyElementaryDiscount

/-! A finite logarithmic upper bound for the genuine supplied-prime series. -/

namespace Entry002

open scoped BigOperators Classical

theorem supply_dyadic_ratio_discount_tail_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1 / 2)
    (N : ℕ) (hN : 1 ≤ ε * (N : ℝ)) :
    (∑' n : ℕ, ((dyadicPrimeBatch P (N + n)).card / (2 : ℝ) ^ (N + n)) *
      ((2 : ℝ) ^ (-ε)) ^ (N + n)) ≤ 32 := by
  have hcap (j : ℕ) :
      (((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j) / 8 ≤ 1 / ((j : ℝ) + 1) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    simpa only [one_div_mul_eq_div] using supply_dyadicPrimeBatch_ratio_le P hP j
  have hh := weakSupply_capped_discount_tail_le_four
    (fun j => (((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j) / 8)
    (fun _ => by positivity) hcap hε hεhi N hN
  simp_rw [weakSupply_discount_eq_rpow, div_mul_eq_mul_div] at hh
  rw [tsum_div_const] at hh
  simp_rw [div_mul_eq_mul_div]
  linarith

/-- No density conclusion is assumed: this upper bound holds for every
fixed local density threshold and every cutoff beyond the reciprocal epsilon. -/
theorem supplyPrimeDirichletSeries_le_good_bin_cutoff (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (δ : ℝ) (hδ : 0 ≤ δ)
    {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1 / 2) (J : ℕ) (hJ : 2 ≤ J)
    (hcut : 1 ≤ ε * ((J : ℝ) + 1)) :
    supplyPrimeDirichletSeries P (1 + ε) ≤
      48 + (δ / Real.log 2) * (1 + Real.log (J : ℝ)) +
        8 * (∑ j ∈ goodDyadicBins P δ J, 1 / ((j : ℝ) + 1)) := by
  have hs := supply_dyadicPrimeBatch_ratio_discount_summable P hP hε
  have htail := supply_dyadic_ratio_discount_tail_le P hP hε hεhi (J + 1)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hcut)
  have hprefix := supply_dyadic_prefix_good_bad_le P hP δ hδ hε J hJ
  have hharm := mul_le_mul_of_nonneg_left
    (weakSupply_harmonic_Icc_two_le_one_add_log J)
    (by positivity : (0 : ℝ) ≤ δ / Real.log 2)
  have hsplit := hs.sum_add_tsum_nat_add (J + 1)
  have hglobal := supplyPrimeDirichletSeries_le_dyadic P hP hε
  simp only [Nat.add_comm] at htail
  rw [← hsplit] at hglobal
  linarith

end Entry002
