import SchurMinimax.ErrorTargets

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rankBudgetWidth_atTop (m n s : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (hs : 0 < s) (hsD : s < m*n) : Tendsto (fun k => rankBudgetWidth m n k s) atTop atTop := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  have ha : Tendsto (fun k : ℕ => (m : ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hm : (1 : ℝ) < m)
  have hu := rankBudgetCollisionWidth_atTop m n s hmp hn hs hsD
  apply tendsto_atTop.2
  intro b
  filter_upwards [ha.eventually_ge_atTop b,hu.eventually_ge_atTop b] with k hk hl
  exact le_min hk hl

theorem natural_packing_width_ratio_limit (d M : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 < w k) (hb : ∀ k, d k ≤ M k ∧ (M k : ℝ) ≤ w k)
    (hd : Tendsto (fun k => (d k : ℝ)/w k) atTop (𝓝 1)) :
    Tendsto (fun k => (M k : ℝ)/w k) atTop (𝓝 1) := by
  have herr : Tendsto (fun k => 1-(M k : ℝ)/w k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sub_nonneg.mpr ((div_le_one (hw k)).mpr (hb k).2))
      (fun k => sub_le_sub_left (div_le_div_of_nonneg_right
        (by exact_mod_cast (hb k).1 : (d k : ℝ) ≤ M k) (hw k).le) 1)
    simpa using Tendsto.const_sub 1 hd
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub herr

theorem natural_error_target_ratio_limit (d M : ℕ → ℕ) (w η : ℕ → ℝ) (β : ℝ)
    (hβ : 0 < β) (hw : ∀ k, 0 < w k)
    (hb : ∀ k, ⌊(d k : ℝ)/β⌋₊ ≤ M k ∧ (M k : ℝ) ≤ η k*w k/β)
    (hd : Tendsto (fun k => (d k : ℝ)/w k) atTop (𝓝 1))
    (hη : Tendsto η atTop (𝓝 1)) (hwinf : Tendsto w atTop atTop) :
    Tendsto (fun k => (M k : ℝ)*β/w k) atTop (𝓝 1) := by
  have hinv : Tendsto (fun k => β/w k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hwinf
  have hlow : Tendsto (fun k => (d k : ℝ)/w k-β/w k) atTop (𝓝 1) := by
    simpa using hd.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hη
  · intro k
    have hf : (d k : ℝ)/β-1 ≤ (M k : ℝ) :=
      (Nat.sub_one_lt_floor _).le.trans (by exact_mod_cast (hb k).1)
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hf hβ.le) (hw k).le
    have he : (((d k : ℝ)/β-1)*β)/w k=(d k : ℝ)/w k-β/w k := by field_simp <;> ring
    rwa [he] at h
  · intro k
    apply (div_le_iff₀ (hw k)).mpr
    have hh := (le_div_iff₀ hβ).mp (hb k).2
    nlinarith

theorem log_nat_ratio_limit (M : ℕ → ℕ) (w : ℕ → ℝ) (hM : ∀ k, 0 < M k)
    (hw : ∀ k, 0 < w k) (h : Tendsto (fun k => (M k : ℝ)/w k) atTop (𝓝 1)) :
    Tendsto (fun k => Real.log (M k : ℝ)-Real.log (w k)) atTop (𝓝 0) := by
  have hh := h.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [] with k
  exact Real.log_div (by exact_mod_cast (hM k).ne') (hw k).ne'

theorem exactRankBudgetMaximum_ratio_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => (exactRankBudgetMaximum C m n k s : ℝ)/rankBudgetWidth m n k s) atTop (𝓝 1) := by
  have hn : 0 < n := hm.trans_le hmn
  apply natural_packing_width_ratio_limit (fun k => rankBudgetPacking m n k s hm)
    (fun k => exactRankBudgetMaximum C m n k s) (fun k => rankBudgetWidth m n k s)
    (fun k => rankBudgetWidth_pos m n k s hm hn hs)
  · intro k
    have h := exactRankBudgetMaximum_bounds C m n k s hm hn hs hsD.le
    exact ⟨h.1,exactRankBudgetTarget_le_width C m n k s _ hm hn hs hsD.le
      (exactRankBudgetMaximum_attained C m n k s hm hn hs hsD.le)⟩
  · exact rankBudgetPacking_ratio_limit m n s hm hmn hs hsD

theorem exactRankBudgetMaximum_log_width_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => Real.log (exactRankBudgetMaximum C m n k s : ℝ)-
      Real.log (rankBudgetWidth m n k s)) atTop (𝓝 0) := by
  apply log_nat_ratio_limit _ _
    (fun k => (exactRankBudgetMaximum_attained C m n k s hm (hm.trans_le hmn) hs hsD.le).1)
    (fun k => rankBudgetWidth_pos m n k s hm (hm.trans_le hmn) hs)
    (exactRankBudgetMaximum_ratio_limit C m n s hm hmn hs hsD)

theorem errorRankBudgetMaximum_ratio_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Tendsto (fun k => (errorRankBudgetMaximum C m n k s ε : ℝ)*(1-ε)/rankBudgetWidth m n k s)
      atTop (𝓝 1) := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  exact natural_error_target_ratio_limit (fun k => rankBudgetPacking m n k s hmp)
    (fun k => errorRankBudgetMaximum C m n k s ε) (fun k => rankBudgetWidth m n k s)
    (fun k => rankBudgetEta m n k s hsD.le) (1-ε) (by linarith)
    (fun k => rankBudgetWidth_pos m n k s hmp hn hs)
    (fun k => errorRankBudgetMaximum_bounds C m n k s hmp hn hs hsD.le ε hε0 hε1)
    (rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD)
    (rankBudgetEta_limit m n s hs hsD.le) (rankBudgetWidth_atTop m n s hm hmn hs hsD)

/-- Actual fixed-error maximal target logarithm; the maximum carries a real
physical protocol witness, independently of minimax supremum attainment. -/
theorem errorRankBudgetMaximum_log_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Tendsto (fun k => Real.log (errorRankBudgetMaximum C m n k s ε : ℝ)-
      (Real.log (rankBudgetWidth m n k s)-Real.log (1-ε))) atTop (𝓝 0) := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  have hβ : (0 : ℝ) < 1-ε := by linarith
  have h := (errorRankBudgetMaximum_ratio_limit C m n s hm hmn hs hsD ε hε0 hε1).log
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [] with k
  have hM : (0 : ℝ) < errorRankBudgetMaximum C m n k s ε := by
    exact_mod_cast (errorRankBudgetMaximum_attained C m n k s hmp hn hs hsD.le ε hε0 hε1).1
  rw [Real.log_div (mul_pos hM hβ).ne' (rankBudgetWidth_pos m n k s hmp hn hs).ne',
    Real.log_mul hM.ne' hβ.ne']
  ring

def rankBudgetLogScale (m n k s : ℕ) : ℝ :=
  (k : ℝ)/2*Real.log ((((m*n : ℕ) : ℝ))/(s : ℝ))-
    ((s*(m*n-s) : ℕ) : ℝ)/2*Real.log (k : ℝ)-Real.log (sharpSupportConstant s (m*n-s))/2

theorem rankBudget_log_rank_error_limit (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    Tendsto (fun k => Real.log ((rankBudgetProjector D k s).rank : ℝ)-
      ((k : ℝ)*Real.log (s : ℝ)+((s*(D-s) : ℕ) : ℝ)*Real.log (k : ℝ)+
        Real.log (sharpSupportConstant s (D-s)))) atTop (𝓝 0) := by
  have h := ((rankBudget_rank_scaled_limit D s hs hsD).log (sharpSupportConstant_pos s (D-s) hs).ne').sub_const
    (Real.log (sharpSupportConstant s (D-s)))
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : (0 : ℝ) < (rankBudgetProjector D k s).rank := by
    exact_mod_cast rankBudgetProjector_rank_pos D k s (hs.trans_le hsD) hs
  rw [Real.log_div hr.ne' (mul_pos (pow_pos hsR _) (pow_pos hkR _)).ne',
    Real.log_mul (pow_ne_zero _ hsR.ne') (pow_ne_zero _ hkR.ne'), Real.log_pow, Real.log_pow]
  ring

theorem rankBudget_log_width_correction_limit (m n s : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hs : 0 < s) (hsD : s < m*n) (hregime : n ≤ m*s) :
    Tendsto (fun k => Real.log (rankBudgetWidth m n k s)-rankBudgetLogScale m n k s)
      atTop (𝓝 0) := by
  have hn : 0 < n := hm.trans_le hmn
  have h := (rankBudget_log_rank_error_limit (m*n) s hs hsD.le).const_mul (-(1/2 : ℝ))
  simp only [mul_zero] at h
  have hA := rankBudgetCollisionWidth_div_local_limit m n s hm hn hs hsD hregime
  apply h.congr'
  filter_upwards [(tendsto_order.1 hA).2 1 (by norm_num),eventually_ge_atTop 1] with k hk hk1
  have haR : (0 : ℝ) < (m^k : ℕ) := by exact_mod_cast pow_pos hm k
  have hau : rankBudgetCollisionWidth m n k s ≤ (m : ℝ)^k := by
    simpa only [Nat.cast_pow] using ((div_lt_one haR).mp hk).le
  have hD : (0 : ℝ) < (m*n : ℕ) := by exact_mod_cast Nat.mul_pos hm hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : (0 : ℝ) < (rankBudgetProjector (m*n) k s).rank := by
    exact_mod_cast rankBudget_rank_pos m n k s hm hn hs
  rw [rankBudgetWidth,min_eq_right hau,rankBudgetCollisionWidth,
    Real.log_sqrt (by positivity),Real.log_div (pow_pos hD _).ne' hr.ne', Real.log_pow]
  unfold rankBudgetLogScale
  rw [Real.log_div hD.ne' hsR.ne']
  ring

/-- The exact target's logarithmic correction, including the threshold n=m*s. -/
theorem exactRankBudgetMaximum_log_correction_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n) (hregime : n ≤ m*s) :
    Tendsto (fun k => Real.log (exactRankBudgetMaximum C m n k s : ℝ)-rankBudgetLogScale m n k s)
      atTop (𝓝 0) := by
  have h := (exactRankBudgetMaximum_log_width_limit C m n s hm hmn hs hsD).add
    (rankBudget_log_width_correction_limit m n s hm hmn hs hsD hregime)
  simpa only [sub_add_sub_cancel, add_zero] using h

theorem rankBudgetPacking_eventually_local (m n s : ℕ) (hm : 0 < m) (hs : 0 < s)
    (hregime : m*s < n) :
    ∀ᶠ k : ℕ in atTop, rankBudgetPacking m n k s hm=m^k ∧ rankBudgetWidth m n k s=(m : ℝ)^k := by
  have hn : 0 < n := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (s : ℝ) < (n : ℝ)/(m : ℝ) := (lt_div_iff₀ hmR).mpr (by exact_mod_cast (by simpa only [Nat.mul_comm] using hregime))
  have h := rankBudgetProjector_rank_div_geometric_limit (m*n) s (Nat.mul_pos hm hn) hs
    ((n : ℝ)/(m : ℝ)) hsR
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
  exact ⟨hd,by rw [rankBudgetWidth,min_eq_left (by simpa only [Nat.cast_pow] using haU)]⟩

theorem exactRankBudgetMaximum_eventually_local (C : RankProtocolClass) (m n s : ℕ)
    (hm : 0 < m) (hs : 0 < s) (hregime : m*s < n) :
    ∀ᶠ k : ℕ in atTop, exactRankBudgetMaximum C m n k s=m^k := by
  have hn : 0 < n := by omega
  have hsD : s ≤ m*n := by nlinarith
  filter_upwards [rankBudgetPacking_eventually_local m n s hm hs hregime] with k hk
  have hb := exactRankBudgetMaximum_bounds C m n k s hm hn hs hsD
  apply le_antisymm
  · have hw : ⌊rankBudgetWidth m n k s⌋₊=m^k := by
      rw [hk.2]
      simp only [← Nat.cast_pow, Nat.floor_natCast]
    exact hb.2.trans_eq hw
  · rw [← hk.1]
    exact hb.1

theorem exactRankBudgetMaximum_isGreatest (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) :
    IsGreatest (exactRankBudgetTargets C m n k s) (exactRankBudgetMaximum C m n k s) :=
  ⟨exactRankBudgetMaximum_attained C m n k s hm hn hs hsD,
    fun K hK => le_csSup (exactRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD).2 hK⟩

theorem errorRankBudgetMaximum_isGreatest (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    IsGreatest (errorRankBudgetTargets C m n k s ε) (errorRankBudgetMaximum C m n k s ε) :=
  ⟨errorRankBudgetMaximum_attained C m n k s hm hn hs hsD ε hε0 hε1,
    fun K hK => le_csSup (errorRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).2 hK⟩

end
end ExtractionSchur
