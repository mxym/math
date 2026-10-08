import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Elementary upper estimates for the weaker supply route. Geometric
discounting beyond a cutoff of size `1/epsilon` costs a fixed constant.
No prime asymptotic, Abelian/Tauberian certificate, or density field is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open scoped BigOperators

noncomputable def weakSupplyDiscount (ε : ℝ) : ℝ :=
  Real.exp (-(Real.log 2) * ε)

theorem weakSupply_log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh

theorem weakSupply_discount_pos_lt_one {ε : ℝ} (hε : 0 < ε) :
    0 < weakSupplyDiscount ε ∧ weakSupplyDiscount ε < 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_one_iff.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith

/-- Uniform reciprocal geometric-gap bound for the actual base two
discount. The explicit constant is independent of any density coefficient. -/
theorem weakSupply_discount_ratio_le_four {ε : ℝ}
    (hε : 0 < ε) (hεhi : ε < 1 / 2) :
    ε / (1 - weakSupplyDiscount ε) ≤ 4 := by
  obtain ⟨hloglo, hloghi⟩ := weakSupply_log_two_bounds
  obtain ⟨hr0, hr1⟩ := weakSupply_discount_pos_lt_one hε
  have hlog0 : 0 < Real.log 2 := by linarith
  have hrhalf : (1 / 2 : ℝ) ≤ weakSupplyDiscount ε := by
    have hx : -(Real.log 2) ≤ -(Real.log 2) * ε := by nlinarith
    have hh := Real.exp_le_exp.mpr hx
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
    norm_num at hh
    simpa only [weakSupplyDiscount, neg_mul] using hh
  have hmul : Real.exp ((Real.log 2) * ε) * weakSupplyDiscount ε = 1 := by
    unfold weakSupplyDiscount
    rw [← Real.exp_add]
    have he : Real.log 2 * ε + -(Real.log 2) * ε = 0 := by ring
    rw [he, Real.exp_zero]
  have hadd := Real.add_one_le_exp ((Real.log 2) * ε)
  have hgap := mul_le_mul_of_nonneg_right hadd hr0.le
  rw [add_mul, one_mul, hmul] at hgap
  have hquarter : (1 / 4 : ℝ) ≤ Real.log 2 * weakSupplyDiscount ε := by
    have hh := mul_le_mul_of_nonneg_right hloglo hr0.le
    nlinarith only [hh, hrhalf]
  have hscaled := mul_le_mul_of_nonneg_left hquarter hε.le
  apply (div_le_iff₀ (by linarith : 0 < 1 - weakSupplyDiscount ε)).mpr
  nlinarith only [hgap, hscaled]

theorem weakSupply_discount_geometric_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => weakSupplyDiscount ε ^ n) :=
  summable_geometric_of_lt_one (weakSupply_discount_pos_lt_one hε).1.le
    (weakSupply_discount_pos_lt_one hε).2

/-- Generic capped nonnegative coefficients are genuinely summable after
discounting; `tsum` is not used with its nonsummable default value. -/
theorem weakSupply_capped_discount_summable (a : ℕ → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (hacap : ∀ j, a j ≤ 1 / ((j : ℝ) + 1))
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => a j * weakSupplyDiscount ε ^ j) := by
  have hr0 := (weakSupply_discount_pos_lt_one hε).1.le
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (ha0 j) (pow_nonneg hr0 j)) _
    (weakSupply_discount_geometric_summable hε)
  intro j
  have ha1 : a j ≤ 1 := (hacap j).trans (by
    apply (div_le_one₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    linarith only [(show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)])
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (pow_nonneg hr0 j)

/-- The actual discounted tail after `N*epsilon >= 1` is at most four,
uniformly in the coefficients and epsilon. -/
theorem weakSupply_capped_discount_tail_le_four (a : ℕ → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (hacap : ∀ j, a j ≤ 1 / ((j : ℝ) + 1))
    {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1 / 2) (N : ℕ)
    (hN : 1 ≤ ε * (N : ℝ)) :
    (∑' n : ℕ, a (N + n) * weakSupplyDiscount ε ^ (N + n)) ≤ 4 := by
  obtain ⟨hr0, hr1⟩ := weakSupply_discount_pos_lt_one hε
  have hN0 : 0 < (N : ℝ) := by nlinarith
  have hcoef (n : ℕ) : a (N + n) ≤ ε := by
    apply (hacap (N + n)).trans
    have hden : 0 < ((N + n : ℕ) : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith only [hN, hε, (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hle (n : ℕ) :
      a (N + n) * weakSupplyDiscount ε ^ (N + n) ≤ ε * weakSupplyDiscount ε ^ n := by
    have hpow : weakSupplyDiscount ε ^ (N + n) ≤ weakSupplyDiscount ε ^ n := by
      rw [pow_add]
      exact mul_le_of_le_one_left (pow_nonneg hr0.le n) (pow_le_one₀ hr0.le hr1.le)
    exact (mul_le_mul_of_nonneg_right (hcoef n) (pow_nonneg hr0.le (N + n))).trans
      (mul_le_mul_of_nonneg_left hpow hε.le)
  have hsmajor : Summable (fun n : ℕ => ε * weakSupplyDiscount ε ^ n) :=
    (weakSupply_discount_geometric_summable hε).mul_left ε
  have hstail : Summable (fun n : ℕ => a (N + n) * weakSupplyDiscount ε ^ (N + n)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 _) (pow_nonneg hr0.le _)) hle hsmajor
  calc
    _ ≤ ∑' n : ℕ, ε * weakSupplyDiscount ε ^ n := hstail.tsum_le_tsum hle hsmajor
    _ = ε / (1 - weakSupplyDiscount ε) := by
      rw [(weakSupply_discount_geometric_summable hε).tsum_mul_left,
        tsum_geometric_of_lt_one hr0.le hr1, div_eq_mul_inv]
    _ ≤ 4 := weakSupply_discount_ratio_le_four hε hεhi

/-- Compatibility with the dyadic Dirichlet factor used by the prime split. -/
theorem weakSupply_discount_eq_rpow (ε : ℝ) :
    weakSupplyDiscount ε = (2 : ℝ) ^ (-ε) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold weakSupplyDiscount
  congr 1
  ring

theorem weakSupply_harmonic_discount_tail_le_four
    {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1 / 2) (N : ℕ)
    (hN : 1 ≤ ε * (N : ℝ)) :
    (∑' n : ℕ, (1 / (((N + n : ℕ) : ℝ) + 1)) *
      ((2 : ℝ) ^ (-ε)) ^ (N + n)) ≤ 4 := by
  have hh := weakSupply_capped_discount_tail_le_four (fun j => 1 / ((j : ℝ) + 1))
    (fun j => by positivity) (fun _ => le_rfl) hε hεhi N hN
  simpa only [weakSupply_discount_eq_rpow] using hh

theorem weakSupply_reciprocal_log_increment {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
  have hi : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by
    field_simp [hx.ne', hx1.ne']
    ring
  rw [hi, Real.log_div hx1.ne' hx.ne'] at hh
  exact hh

/-- Elementary logarithmic upper bound for the exact positive-index finite
harmonic interval used by the good/bad dyadic-bin decomposition. -/
theorem weakSupply_harmonic_Icc_two_le_one_add_log (J : ℕ) :
    (∑ j ∈ Finset.Icc 2 J, 1 / ((j : ℝ) + 1)) ≤ 1 + Real.log (J : ℝ) := by
  have hsum (n : ℕ) : (∑ j ∈ Finset.Icc 1 n, 1 / ((j : ℝ) + 1)) ≤
      Real.log ((n : ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hh := weakSupply_reciprocal_log_increment
        (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      push_cast
      linarith only [ih, hh]
  by_cases hJ0 : J = 0
  · simp [hJ0]
  have hJ1 : 1 ≤ J := by omega
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hsubset : Finset.Icc 2 J ⊆ Finset.Icc 1 J := by
    intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun j _ _ => by positivity : ∀ j ∈ Finset.Icc 1 J, j ∉ Finset.Icc 2 J →
      0 ≤ 1 / ((j : ℝ) + 1))
  have hJcast : (J : ℝ) + 1 ≤ 2 * (J : ℝ) := by
    have hh : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (J : ℝ) + 1) hJcast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hJpos.ne'] at hlog
  have hlog2 := weakSupply_log_two_bounds.2
  exact hmass.trans ((hsum J).trans (by linarith only [hlog, hlog2]))

end Entry002
