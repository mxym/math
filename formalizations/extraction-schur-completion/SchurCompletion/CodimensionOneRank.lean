import SchurCompletion.WordStraightening

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

theorem choose_div_self_pow_limit (s : ℕ) :
    Tendsto (fun k : ℕ => (k.choose s : ℝ)/(k : ℝ)^s) atTop
      (𝓝 ((s.factorial : ℝ)⁻¹)) := by
  have h := (isEquivalent_choose s).div
    (IsEquivalent.refl (u := fun k : ℕ => (k : ℝ)^s))
  have he : (fun k : ℕ => ((k : ℝ)^s / (s.factorial : ℝ))/(k : ℝ)^s) =ᶠ[atTop]
      (fun _ => (s.factorial : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    field_simp
  exact (h.trans he.isEquivalent).tendsto_nhds_iff.mpr tendsto_const_nhds

theorem choose_div_higher_pow_limit (j s : ℕ) (hjs : j < s) :
    Tendsto (fun k : ℕ => (k.choose j : ℝ)/(k : ℝ)^s) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun k => by positivity)) _
    (tendsto_const_div_pow 1 (s-j) (by omega))
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  apply (div_le_div_iff₀ (pow_pos hkR s) (pow_pos hkR (s-j))).mpr
  have hc : (k.choose j : ℝ) ≤ (k : ℝ)^j := by exact_mod_cast Nat.choose_le_pow k j
  calc
    _ ≤ (k : ℝ)^j * (k : ℝ)^(s-j) := by gcongr
    _ = 1 * (k : ℝ)^s := by rw [← pow_add, show j+(s-j) = s by omega, one_mul]

theorem normalized_pattern_term (s k j : ℕ) (hs : 0 < s) (hj : j ≤ k) :
    (k.choose j : ℝ) * (s : ℝ)^(k-j) / ((s : ℝ)^k * (k : ℝ)^s) =
      ((k.choose j : ℝ)/(k : ℝ)^s)/(s : ℝ)^j := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hp : (s : ℝ)^k = (s : ℝ)^(k-j) * (s : ℝ)^j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  rw [hp]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.le_zero] at hj
    subst j
    simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    field_simp

theorem patternPolynomial_codimension_one_scaled_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (patternPolynomial s k (s+1) : ℝ) /
      ((s : ℝ)^k * (k : ℝ)^s)) atTop
      (𝓝 (((s : ℝ)^s * (s.factorial : ℝ))⁻¹)) := by
  have hlow (j : ℕ) (hj : j < s) :
      Tendsto (fun k : ℕ => (k.choose j : ℝ) * (s : ℝ)^(k-j) /
        ((s : ℝ)^k * (k : ℝ)^s)) atTop (𝓝 0) := by
    have h := (choose_div_higher_pow_limit j s hj).div_const ((s : ℝ)^j)
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop j] with k hk
    exact (normalized_pattern_term s k j hs hk).symm
  have hsum : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range s,
      (k.choose j : ℝ) * (s : ℝ)^(k-j) / ((s : ℝ)^k * (k : ℝ)^s)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range s)
      (fun j hj => hlow j (Finset.mem_range.mp hj))
  have htop : Tendsto (fun k : ℕ => (k.choose s : ℝ) * (s : ℝ)^(k-s) /
      ((s : ℝ)^k * (k : ℝ)^s)) atTop
      (𝓝 (((s : ℝ)^s * (s.factorial : ℝ))⁻¹)) := by
    have h := (choose_div_self_pow_limit s).div_const ((s : ℝ)^s)
    have hcEq : (s.factorial : ℝ)⁻¹ / (s : ℝ)^s =
        ((s : ℝ)^s * (s.factorial : ℝ))⁻¹ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    rw [hcEq] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop s] with k hk
    exact (normalized_pattern_term s k s hs hk).symm
  have h := hsum.add htop
  simpa only [zero_add, patternPolynomial, Finset.sum_range_succ, Nat.cast_add,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, add_div, Finset.sum_div] using h

/-- Sharp actual rank asymptotic for the complete codimension-one subfamily,
obtained by straightening above and the actual Haar purity below. -/
theorem rankBudget_codimension_one_rank_scaled_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector (s+1) k s).rank : ℝ) /
      ((s : ℝ)^k * (k : ℝ)^s)) atTop
      (𝓝 (((s : ℝ)^s * (s.factorial : ℝ))⁻¹)) := by
  let c : ℝ := ((s : ℝ)^s * (s.factorial : ℝ))⁻¹
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < (c-a)/2 := by linarith
    filter_upwards [rankBudget_codimension_one_sharp_lower s hs ((c-a)/2) hε] with k hk
    change c - (c-a)/2 ≤ _ at hk
    linarith
  · intro b hb
    have hu := (tendsto_order.1 (patternPolynomial_codimension_one_scaled_limit s hs)).2 b hb
    filter_upwards [hu] with k hk
    apply lt_of_le_of_lt _ hk
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast rankBudget_codimension_one_rank_upper s k) (by positivity)

/-- The actual support rank times the literal Haar purity tends to one,
for every fixed positive codimension-one rank budget. -/
theorem rankBudget_codimension_one_rank_times_purity_limit (s : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector (s+1) k s).rank : ℝ) *
      (flatHaarAverage (s+1) s k (Nat.le_succ s) *
        flatHaarAverage (s+1) s k (Nat.le_succ s)).trace.re) atTop (𝓝 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : (0 : ℝ) < (s : ℝ)^s * (s.factorial : ℝ) := by positivity
  have h := (rankBudget_codimension_one_rank_scaled_limit s hs).mul
    (flatHaarAverage_codimension_one_purity_scaled_limit s hs)
  rw [inv_mul_cancel₀ hC.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  field_simp


theorem rankBudget_codimension_one_rank_isEquivalent (s : ℕ) (hs : 0 < s) :
    (fun k : ℕ => ((rankBudgetProjector (s+1) k s).rank : ℝ)) ~[atTop]
      (fun k : ℕ => (((s : ℝ)^s * (s.factorial : ℝ))⁻¹) *
        ((s : ℝ)^k * (k : ℝ)^s)) := by
  let c : ℝ := ((s : ℝ)^s * (s.factorial : ℝ))⁻¹
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hc : 0 < c := by dsimp [c]; positivity
  have hn : ∀ᶠ k : ℕ in atTop, c * ((s : ℝ)^k * (k : ℝ)^s) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  rw [isEquivalent_iff_tendsto_one hn]
  have h := (rankBudget_codimension_one_rank_scaled_limit s hs).div_const c
  change Tendsto _ atTop (𝓝 (c/c)) at h
  rw [div_self hc.ne'] at h
  apply h.congr'
  filter_upwards [] with k
  simp [Pi.div_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end
end ExtractionSchur
