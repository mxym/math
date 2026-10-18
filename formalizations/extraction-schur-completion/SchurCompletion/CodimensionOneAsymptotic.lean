import SchurCompletion.CodimensionOneMoments
import SymmetricSupport.RankAsymptotic

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

def betaBinomial (s k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),
    ((s+j).choose j : ℝ)⁻¹ * z ^ (k-j) * (k.choose j : ℝ)

theorem choose_mul_inverse_choose (s k j : ℕ) (hj : j ≤ k) :
    ((s+k).choose s : ℝ) * (((s+j).choose j : ℝ)⁻¹ * (k.choose j : ℝ)) =
      ((s+k).choose (k-j) : ℝ) := by
  have h := Nat.choose_mul (n := s+k) (k := k) (s := k-j) (Nat.sub_le k j)
  rw [Nat.choose_symm hj, show s+k-(k-j) = s+j by omega,
    show k-(k-j) = j by omega, ← Nat.choose_symm_add] at h
  have hn : ((s+j).choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (show j ≤ s+j by omega))
  have hR : ((s+k).choose s : ℝ) * (k.choose j : ℝ) =
      ((s+k).choose (k-j) : ℝ) * ((s+j).choose j : ℝ) := by
    exact_mod_cast h
  calc
    _ = (((s+k).choose s : ℝ) * (k.choose j : ℝ)) /
        ((s+j).choose j : ℝ) := by ring
    _ = _ := by rw [hR]; exact mul_div_cancel_right₀ _ hn

theorem betaBinomial_mul_choose (s k : ℕ) (z : ℝ) :
    betaBinomial s k z * ((s+k).choose s : ℝ) =
      ∑ i ∈ Finset.range (k+1), ((s+k).choose i : ℝ) * z ^ i := by
  unfold betaBinomial
  rw [Finset.sum_mul]
  have he : (∑ j ∈ Finset.range (k+1),
      ((s+j).choose j : ℝ)⁻¹ * z ^ (k-j) * (k.choose j : ℝ) *
        ((s+k).choose s : ℝ)) =
      ∑ j ∈ Finset.range (k+1), ((s+k).choose (k-j) : ℝ) * z ^ (k-j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hh := choose_mul_inverse_choose s k j (by simpa using Finset.mem_range.mp hj)
    calc
      _ = (((s+k).choose s : ℝ) *
          (((s+j).choose j : ℝ)⁻¹ * (k.choose j : ℝ))) * z ^ (k-j) := by ring
      _ = _ := by rw [hh]
  rw [he]
  simpa only [Nat.add_sub_cancel] using
    (Finset.sum_range_reflect (fun i => ((s+k).choose i : ℝ) * z ^ i) (k+1))

/-- Exact cancellation turns the full beta-binomial moment into a binomial
main term minus only s tail terms. -/
theorem betaBinomial_main_sub_tail (s k : ℕ) (z : ℝ) :
    betaBinomial s k z * ((s+k).choose s : ℝ) =
      (z+1) ^ (s+k) -
        ∑ i ∈ Finset.range s, ((s+k).choose (s-1-i) : ℝ) * z ^ (k+1+i) := by
  have hfull : (z+1) ^ (s+k) =
      ∑ i ∈ Finset.range (s+k+1), ((s+k).choose i : ℝ) * z ^ i := by
    rw [add_pow]
    simp only [one_pow, mul_one, mul_comm]
  have hsplit := Finset.sum_range_add
    (fun i => ((s+k).choose i : ℝ) * z ^ i) (k+1) s
  have htail : (∑ i ∈ Finset.range s,
      ((s+k).choose (k+1+i) : ℝ) * z ^ (k+1+i)) =
      ∑ i ∈ Finset.range s, ((s+k).choose (s-1-i) : ℝ) * z ^ (k+1+i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← Nat.choose_symm (show k+1+i ≤ s+k by omega),
      show s+k-(k+1+i) = s-1-i by omega]
  rw [show k+1+s = s+k+1 by omega, htail] at hsplit
  rw [betaBinomial_mul_choose, hfull, hsplit]
  ring

theorem flatHaarAverage_codimension_one_purity_re (s k : ℕ) :
    (flatHaarAverage (s+1) s k (Nat.le_succ s) *
      flatHaarAverage (s+1) s k (Nat.le_succ s)).trace.re =
      ((s : ℝ)⁻¹ ^ 2) ^ k * betaBinomial s k ((s : ℝ)-1) := by
  have h := congrArg Complex.re (flatHaarAverage_codimension_one_purity s k)
  simpa [betaBinomial, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum] using h


theorem tendsto_choose_shift_mul_geometric (s d : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => ((s+k).choose d : ℝ) * q ^ k) atTop (𝓝 0) := by
  have hb := (tendsto_pow_const_mul_const_pow_of_lt_one d hq hq1).const_mul ((2 : ℝ)^d)
  simp only [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun k => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg hq _))) _ hb
  filter_upwards [eventually_ge_atTop s] with k hk
  have hsk : ((s+k : ℕ) : ℝ) ≤ 2*(k : ℝ) := by exact_mod_cast (by omega : s+k ≤ 2*k)
  have hc : ((s+k).choose d : ℝ) ≤ ((s+k : ℕ) : ℝ)^d := by
    exact_mod_cast Nat.choose_le_pow (s+k) d
  calc
    _ ≤ (((s+k : ℕ) : ℝ)^d) * q^k := by gcongr
    _ ≤ (2*(k : ℝ))^d * q^k := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem betaBinomial_scaled_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => betaBinomial s k ((s : ℝ)-1) *
      ((s+k).choose s : ℝ) / (s : ℝ)^k) atTop (𝓝 ((s : ℝ)^s)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let q : ℝ := ((s : ℝ)-1)/(s : ℝ)
  have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hq : 0 ≤ q := div_nonneg (by linarith) hsR.le
  have hq1 : q < 1 := (div_lt_one hsR).mpr (by linarith)
  have ht (i : ℕ) : Tendsto (fun k : ℕ => ((s+k).choose (s-1-i) : ℝ) *
      ((s : ℝ)-1)^(1+i) * q^k) atTop (𝓝 0) := by
    have h := (tendsto_choose_shift_mul_geometric s (s-1-i) q hq hq1).mul_const
      (((s : ℝ)-1)^(1+i))
    simpa only [zero_mul, mul_right_comm] using h
  have htail : Tendsto (fun k : ℕ => ∑ i ∈ Finset.range s,
      ((s+k).choose (s-1-i) : ℝ) * ((s : ℝ)-1)^(1+i) * q^k) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.range s) (fun i hi => ht i)
  have hlim := (tendsto_const_nhds (x := (s : ℝ)^s)).sub htail
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with k
  rw [betaBinomial_main_sub_tail, sub_add_cancel, sub_div, pow_add,
    mul_div_cancel_right₀ _ (pow_ne_zero k hsR.ne'), Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show k+1+i = (1+i)+k by omega, pow_add]
  dsimp [q]
  rw [div_pow]
  ring


/-- The genuine codimension-one Haar purity has the manuscript's sharp
constant, established without a Young decomposition or concentration premise. -/
theorem flatHaarAverage_codimension_one_purity_scaled_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (s : ℝ)^k * (k : ℝ)^s *
      (flatHaarAverage (s+1) s k (Nat.le_succ s) *
        flatHaarAverage (s+1) s k (Nat.le_succ s)).trace.re)
      atTop (𝓝 ((s : ℝ)^s * (s.factorial : ℝ))) := by
  have hc : Tendsto (fun k : ℕ => ((s+k).choose s : ℝ) / (k : ℝ)^s)
      atTop (𝓝 (1 / (s.factorial : ℝ))) := by
    have h := symmetricProjector_rank_scaled_limit (s+1) (by omega)
    have hh (k : ℕ) : (symmetricProjector (s+1) k).rank = (s+k).choose s := by
      rw [symmetricProjector_rank_choose_complement (s+1) k (by omega)]
      congr 1 <;> omega
    simpa only [hh, Nat.add_sub_cancel] using h
  have hlim := (betaBinomial_scaled_limit s hs).div hc (by positivity)
  simp [div_eq_mul_inv] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hcR : ((s+k).choose s : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show s ≤ s+k by omega)
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [flatHaarAverage_codimension_one_purity_re,
    pow_right_comm (s : ℝ)⁻¹ 2 k, inv_pow]
  field_simp [hsR, hkR, hcR]
  <;> ring


theorem flatHaarAverage_codimension_one_purity_isEquivalent (s : ℕ) (hs : 0 < s) :
    (fun k : ℕ => (flatHaarAverage (s+1) s k (Nat.le_succ s) *
      flatHaarAverage (s+1) s k (Nat.le_succ s)).trace.re) ~[atTop]
      (fun k : ℕ => ((s : ℝ)^s * (s.factorial : ℝ)) /
        ((s : ℝ)^k * (k : ℝ)^s)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : (0 : ℝ) < (s : ℝ)^s * (s.factorial : ℝ) := by positivity
  have hn : ∀ᶠ k : ℕ in atTop,
      ((s : ℝ)^s * (s.factorial : ℝ)) / ((s : ℝ)^k * (k : ℝ)^s) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  rw [isEquivalent_iff_tendsto_one hn]
  have hlim := (flatHaarAverage_codimension_one_purity_scaled_limit s hs).div_const
    ((s : ℝ)^s * (s.factorial : ℝ))
  rw [div_self hC.ne'] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp [Pi.div_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- A sharp leading lower bound on the actual support rank follows already
from the actual Haar purity. The matching rank upper bound is separate. -/
theorem rankBudget_codimension_one_sharp_lower (s : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (((s : ℝ)^s * (s.factorial : ℝ))⁻¹ - ε) ≤
        ((rankBudgetProjector (s+1) k s).rank : ℝ) /
          ((s : ℝ)^k * (k : ℝ)^s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : (0 : ℝ) < (s : ℝ)^s * (s.factorial : ℝ) := by positivity
  have hlim := (flatHaarAverage_codimension_one_purity_scaled_limit s hs).inv₀ hC.ne'
  have hlower := (tendsto_order.1 hlim).1
    (((s : ℝ)^s * (s.factorial : ℝ))⁻¹ - ε) (by linarith)
  filter_upwards [hlower, eventually_ge_atTop 1] with k hk hk1
  apply le_trans hk.le
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let scale : ℝ := (s : ℝ)^k * (k : ℝ)^s
  have hscale : 0 < scale := mul_pos (pow_pos hsR _) (pow_pos hkR _)
  let p := (flatHaarAverage (s+1) s k (Nat.le_succ s) *
    flatHaarAverage (s+1) s k (Nat.le_succ s)).trace.re
  have hRP : 1 ≤ ((rankBudgetProjector (s+1) k s).rank : ℝ) * p := by
    have h := haarOrbitAverage_rank_times_purity_ge_one (s+1) k
      (flatCoordinateDensity (s+1) s (Nat.le_succ s))
      (flatCoordinateDensity_density (s+1) s hs (Nat.le_succ s))
    simpa only [flatCoordinateDensity_rank (s+1) s hs (Nat.le_succ s), p, flatHaarAverage] using h
  have hp : 0 < p := by
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℝ) ≤ (rankBudgetProjector (s+1) k s).rank by positivity)
      (le_of_not_gt hn)
    linarith
  change (scale * p)⁻¹ ≤ ((rankBudgetProjector (s+1) k s).rank : ℝ) / scale
  rw [← one_div, div_le_div_iff₀ (mul_pos hscale hp) hscale]
  have h := mul_le_mul_of_nonneg_left hRP hscale.le
  nlinarith

end
end ExtractionSchur
