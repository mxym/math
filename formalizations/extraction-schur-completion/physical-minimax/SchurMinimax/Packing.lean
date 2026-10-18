import SchurMinimax.Finite
import RankSupport.FirstOrder

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section

def rankBudgetCollisionWidth (m n k s : ℕ) : ℝ :=
  Real.sqrt ((((m*n : ℕ) : ℝ)^k)/((rankBudgetProjector (m*n) k s).rank : ℝ))

def rankBudgetWidth (m n k s : ℕ) : ℝ := min ((m : ℝ)^k) (rankBudgetCollisionWidth m n k s)

def rankBudgetPacking (m n k s : ℕ) (hm : 0 < m) : ℕ :=
  packingDimension (m^k) (n^k) (rankBudgetProjector (m*n) k s).rank (pow_pos hm _)
    (by simpa only [mul_pow] using rankBudgetProjector_rank_le_dimension (m*n) k s)

theorem rankBudget_rank_pos (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) :
    0 < (rankBudgetProjector (m*n) k s).rank :=
  rankBudgetProjector_rank_pos (m*n) k s (Nat.mul_pos hm hn) hs

theorem rankBudgetCollisionWidth_pos (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) :
    0 < rankBudgetCollisionWidth m n k s := by
  unfold rankBudgetCollisionWidth
  apply Real.sqrt_pos.mpr
  exact div_pos (pow_pos (by exact_mod_cast Nat.mul_pos hm hn) _)
    (by exact_mod_cast rankBudget_rank_pos m n k s hm hn hs)

theorem rankBudgetCollisionWidth_sq (m n k s : ℕ) :
    (rankBudgetCollisionWidth m n k s)^2 =
      (((m*n : ℕ) : ℝ)^k)/((rankBudgetProjector (m*n) k s).rank : ℝ) := by
  exact Real.sq_sqrt (by positivity)

theorem rankBudgetCollisionWidth_budget (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) :
    ((rankBudgetProjector (m*n) k s).rank : ℝ)*(rankBudgetCollisionWidth m n k s)^2 =
      ((m^k : ℕ) : ℝ)*((n^k : ℕ) : ℝ) := by
  rw [rankBudgetCollisionWidth_sq]
  have hr : ((rankBudgetProjector (m*n) k s).rank : ℝ) ≠ 0 :=
    (show (0 : ℝ) < _ by exact_mod_cast rankBudget_rank_pos m n k s hm hn hs).ne'
  rw [mul_div_cancel₀ _ hr]
  push_cast
  exact mul_pow _ _ _

theorem rankBudgetPacking_properties (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) :
    0 < rankBudgetPacking m n k s hm ∧
      (rankBudgetPacking m n k s hm : ℝ) ≤ rankBudgetWidth m n k s ∧
      (rankBudgetProjector (m*n) k s).rank ≤
        (m^k/rankBudgetPacking m n k s hm)*(n^k/rankBudgetPacking m n k s hm) := by
  have h := packingDimension_properties (a := m^k) (b := n^k)
    (r := (rankBudgetProjector (m*n) k s).rank) (pow_pos hm k)
    (by simpa only [mul_pow] using rankBudgetProjector_rank_le_dimension (m*n) k s)
  refine ⟨h.1,le_min ?_ ?_,h.2.2⟩
  · exact_mod_cast h.2.1
  · exact feasible_dimension_real_bound (rankBudget_rank_pos m n k s hm hn hs)
      (rankBudgetCollisionWidth_pos m n k s hm hn hs).le
      (rankBudgetCollisionWidth_budget m n k s hm hn hs) h.2.2

theorem rankBudgetWidth_pos (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) :
    0 < rankBudgetWidth m n k s :=
  lt_min (pow_pos (by exact_mod_cast hm) _) (rankBudgetCollisionWidth_pos m n k s hm hn hs)

theorem real_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.sqrt (x^k)=(Real.sqrt x)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

theorem rankBudgetCollisionWidth_atTop (m n s : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => rankBudgetCollisionWidth m n k s) atTop atTop := by
  have hD : (0 : ℝ) < (m*n : ℕ) := by exact_mod_cast Nat.mul_pos hm hn
  have he (k : ℕ) : rankBudgetCollisionWidth m n k s =
      (Real.sqrt ((m*n : ℕ) : ℝ))^k/Real.sqrt ((rankBudgetProjector (m*n) k s).rank : ℝ) := by
    rw [rankBudgetCollisionWidth, Real.sqrt_div (by positivity), real_sqrt_pow _ hD.le]
  simp_rw [he]
  apply rankBudgetProjector_geometric_div_sqrt_rank_atTop (m*n) s (Nat.mul_pos hm hn) hs _
    (Real.sqrt_pos.mpr hD)
  rw [Real.sq_sqrt hD.le]
  exact_mod_cast hsD

theorem rankBudget_power_div_rank_limit (D s : ℕ) (hs : 0 < s) (hsD : s < D) :
    Tendsto (fun k : ℕ => (s : ℝ)^k/((rankBudgetProjector D k s).rank : ℝ)) atTop (𝓝 0) := by
  have hg : s*(D-s) ≠ 0 := (Nat.mul_pos hs (Nat.sub_pos_of_lt hsD)).ne'
  have hpow : Tendsto (fun k : ℕ => (k : ℝ)^(s*(D-s))) atTop atTop :=
    (tendsto_pow_atTop hg).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_inv_atTop_zero.comp hpow).div
    (rankBudget_rank_scaled_limit D s hs hsD.le) (sharpSupportConstant_pos s (D-s) hs).ne'
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : (0 : ℝ) < (rankBudgetProjector D k s).rank := by
    exact_mod_cast rankBudgetProjector_rank_pos D k s (hs.trans hsD) hs
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp

theorem rankBudgetCollisionWidth_div_local_limit (m n s : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s < m*n) (hregime : n ≤ m*s) :
    Tendsto (fun k => rankBudgetCollisionWidth m n k s/((m^k : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hbound := Real.continuous_sqrt.continuousAt.tendsto.comp
    (rankBudget_power_div_rank_limit (m*n) s hs hsD)
  simp only [Real.sqrt_zero] at hbound
  apply squeeze_zero (fun k => div_nonneg (Real.sqrt_nonneg _) (by positivity)) _ hbound
  intro k
  have haR : (0 : ℝ) < (m^k : ℕ) := by exact_mod_cast pow_pos hm k
  have hrR : (0 : ℝ) < (rankBudgetProjector (m*n) k s).rank := by
    exact_mod_cast rankBudget_rank_pos m n k s hm hn hs
  have he : (rankBudgetCollisionWidth m n k s/((m^k : ℕ) : ℝ))^2 =
      (((n^k : ℕ) : ℝ)/((m^k : ℕ) : ℝ))/((rankBudgetProjector (m*n) k s).rank : ℝ) := by
    rw [div_pow, rankBudgetCollisionWidth_sq]
    push_cast
    rw [mul_pow]
    field_simp
  have hba : ((n^k : ℕ) : ℝ)/((m^k : ℕ) : ℝ) ≤ (s : ℝ)^k := by
    apply (div_le_iff₀ haR).mpr
    have hnat : n^k ≤ (m*s)^k := Nat.pow_le_pow_left hregime k
    exact_mod_cast (by simpa only [mul_pow, Nat.mul_comm] using hnat)
  have hsq : (rankBudgetCollisionWidth m n k s/((m^k : ℕ) : ℝ))^2 ≤
      (Real.sqrt ((s : ℝ)^k/((rankBudgetProjector (m*n) k s).rank : ℝ)))^2 := by
    rw [he, Real.sq_sqrt (by positivity)]
    exact div_le_div_of_nonneg_right hba hrR.le
  exact (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) haR.le) (Real.sqrt_nonneg _)).mp hsq

theorem rankBudgetPacking_ratio_entropy_limit (m n s : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hs : 0 < s) (hsD : s < m*n) (hregime : n ≤ m*s) :
    Tendsto (fun k => (rankBudgetPacking m n k s hm : ℝ)/rankBudgetWidth m n k s) atTop (𝓝 1) := by
  have hn : 0 < n := hm.trans_le hmn
  have hA := rankBudgetCollisionWidth_div_local_limit m n s hm hn hs hsD hregime
  have hB : Tendsto (fun k => rankBudgetCollisionWidth m n k s/((n^k : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg (Real.sqrt_nonneg _) (by positivity)) _ hA
    intro k
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by exact_mod_cast pow_pos hm k)
    exact_mod_cast Nat.pow_le_pow_left hmn k
  have h := packing_ratio_tendsto (a := fun k => m^k) (b := fun k => n^k)
    (r := fun k => (rankBudgetProjector (m*n) k s).rank)
    (w := fun k => rankBudgetCollisionWidth m n k s)
    (fun k => pow_pos hm k) (fun k => pow_pos hn k)
    (fun k => rankBudget_rank_pos m n k s hm hn hs)
    (fun k => by simpa only [mul_pow] using rankBudgetProjector_rank_le_dimension (m*n) k s)
    (fun k => rankBudgetCollisionWidth_pos m n k s hm hn hs)
    (fun k => rankBudgetCollisionWidth_budget m n k s hm hn hs)
    (rankBudgetCollisionWidth_atTop m n s hm hn hs hsD) hA hB
  apply h.congr'
  filter_upwards [(tendsto_order.1 hA).2 1 (by norm_num)] with k hk
  have haR : (0 : ℝ) < (m^k : ℕ) := by exact_mod_cast pow_pos hm k
  have haW : rankBudgetCollisionWidth m n k s ≤ (m : ℝ)^k := by
    simpa only [Nat.cast_pow] using ((div_lt_one haR).mp hk).le
  rw [rankBudgetWidth, min_eq_right haW]
  rfl

theorem rankBudgetPacking_ratio_local_limit (m n s : ℕ) (hm : 0 < m) (hs : 0 < s)
    (hregime : m*s < n) :
    Tendsto (fun k => (rankBudgetPacking m n k s hm : ℝ)/rankBudgetWidth m n k s) atTop (𝓝 1) := by
  have hn : 0 < n := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (s : ℝ) < (n : ℝ)/(m : ℝ) := (lt_div_iff₀ hmR).mpr (by exact_mod_cast (by simpa only [Nat.mul_comm] using hregime))
  have h := rankBudgetProjector_rank_div_geometric_limit (m*n) s (Nat.mul_pos hm hn) hs
    ((n : ℝ)/(m : ℝ)) hsR
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_order.1 h).2 1 (by norm_num)] with k hk
  have hmK : (0 : ℝ) < (m^k : ℕ) := by exact_mod_cast pow_pos hm k
  have hnK : (0 : ℝ) < (n^k : ℕ) := by exact_mod_cast pow_pos hn k
  have hrK : (0 : ℝ) < (rankBudgetProjector (m*n) k s).rank := by
    exact_mod_cast rankBudget_rank_pos m n k s hm hn hs
  have hreal : ((rankBudgetProjector (m*n) k s).rank : ℝ)*((m^k : ℕ) : ℝ) ≤ ((n^k : ℕ) : ℝ) := by
    have hh := (div_lt_one (pow_pos (div_pos hnR hmR) k)).mp hk
    rw [div_pow] at hh
    have hh' := (lt_div_iff₀ (pow_pos hmR k)).mp hh
    exact_mod_cast hh'.le
  have hnat : (rankBudgetProjector (m*n) k s).rank*(m^k) ≤ n^k := by exact_mod_cast hreal
  have hfeas : (rankBudgetProjector (m*n) k s).rank ≤ (m^k/(m^k))*(n^k/(m^k)) := by
    rw [Nat.div_self (pow_pos hm k), one_mul]
    exact (Nat.le_div_iff_mul_le (pow_pos hm k)).mpr hnat
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have hd : rankBudgetPacking m n k s hm=m^k := by
    apply le_antisymm
    · exact (packingDimension_properties (pow_pos hm k)
        (show (rankBudgetProjector (m*n) k s).rank ≤ m^k*n^k by
          simpa only [mul_pow] using rankBudgetProjector_rank_le_dimension (m*n) k s)).2.1
    · exact feasible_le_packingDimension (pow_pos hm k)
        (show (rankBudgetProjector (m*n) k s).rank ≤ m^k*n^k by
          simpa only [mul_pow] using rankBudgetProjector_rank_le_dimension (m*n) k s)
        (pow_pos hm k) le_rfl hfeas
  have haU : ((m^k : ℕ) : ℝ) ≤ rankBudgetCollisionWidth m n k s := by
    apply (sq_le_sq₀ hmK.le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    apply (le_div_iff₀ hrK).mpr
    have hh := mul_le_mul_of_nonneg_left hreal hmK.le
    push_cast at hh ⊢
    rw [mul_pow]
    nlinarith
  rw [hd, rankBudgetWidth, min_eq_left (by simpa only [Nat.cast_pow] using haU), Nat.cast_pow,
    div_self (pow_ne_zero k hmR.ne')]

theorem rankBudgetPacking_ratio_limit (m n s : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => (rankBudgetPacking m n k s hm : ℝ)/rankBudgetWidth m n k s) atTop (𝓝 1) := by
  by_cases hregime : n ≤ m*s
  · exact rankBudgetPacking_ratio_entropy_limit m n s hm hmn hs hsD hregime
  · exact rankBudgetPacking_ratio_local_limit m n s hm hs (by omega)

end
end ExtractionSchur
