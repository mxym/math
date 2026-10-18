import SchurMinimax.FlatOrbit

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual protocols that meet the fixed-error threshold on every orientation
of the flat rank-s spectrum. -/
def flatOrbitErrorTargets (C : RankProtocolClass) (m n k s : ℕ) (hsD : s ≤ m*n)
    (ε : ℝ) : Set ℕ :=
  {K | 0 < K ∧ ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ U : OneCopyUnitary (m*n), 1-ε ≤ V.fidelity (tensorInput m n k
      ((U : Matrix _ _ ℂ)*flatCoordinateDensity (m*n) s hsD*(U : Matrix _ _ ℂ)ᴴ))}

def flatOrbitErrorMaximum (C : RankProtocolClass) (m n k s : ℕ) (hsD : s ≤ m*n)
    (ε : ℝ) : ℕ := sSup (flatOrbitErrorTargets C m n k s hsD ε)

theorem errorRankBudgetTargets_subset_flatOrbit (C : RankProtocolClass) (m n k s : ℕ)
    (hs : 0 < s) (hsD : s ≤ m*n) (ε : ℝ) :
    errorRankBudgetTargets C m n k s ε ⊆ flatOrbitErrorTargets C m n k s hsD ε := by
  rintro K ⟨hK,V,hC,hV⟩
  exact ⟨hK,V,hC,fun U => hV (rankBudgetOrbitInput (m*n) s hs hsD U)⟩

theorem flatOrbitErrorTarget_le_budget (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε : ε < 1) (hK : K ∈ flatOrbitErrorTargets C m n k s hsD ε) :
    (K : ℝ) ≤ rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε) := by
  obtain ⟨hK,V,hC,hV⟩ := hK
  have h := orbit_guarantee_le_haar m n k K (flatCoordinateDensity (m*n) s hsD) V (1-ε) hV
  have hh := h.trans ((physicalHaarAverage_fidelity_upper_profile m n k s K hm hn hs hsD hK V).trans
    (min_le_right _ _))
  have hmul := (le_div_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)).mp hh
  exact (le_div_iff₀ (by linarith : (0 : ℝ) < 1-ε)).mpr (by nlinarith)

theorem flatOrbitErrorTargets_nonempty_bdd (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (flatOrbitErrorTargets C m n k s hsD ε).Nonempty ∧
      BddAbove (flatOrbitErrorTargets C m n k s hsD ε) := by
  constructor
  · obtain ⟨K,hK⟩ := (errorRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).1
    exact ⟨K,errorRankBudgetTargets_subset_flatOrbit C m n k s hs hsD ε hK⟩
  · refine ⟨⌊rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε)⌋₊,fun K hK => ?_⟩
    exact Nat.le_floor (flatOrbitErrorTarget_le_budget C m n k s K hm hn hs hsD ε hε1 hK)

theorem flatOrbitErrorMaximum_attained (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    flatOrbitErrorMaximum C m n k s hsD ε ∈ flatOrbitErrorTargets C m n k s hsD ε :=
  Nat.sSup_mem (flatOrbitErrorTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).1
    (flatOrbitErrorTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).2

theorem flatOrbitErrorMaximum_isGreatest (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    IsGreatest (flatOrbitErrorTargets C m n k s hsD ε) (flatOrbitErrorMaximum C m n k s hsD ε) :=
  ⟨flatOrbitErrorMaximum_attained C m n k s hm hn hs hsD ε hε0 hε1,
    fun K hK => le_csSup (flatOrbitErrorTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).2 hK⟩

theorem flatOrbitErrorMaximum_bounds (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ⌊(rankBudgetPacking m n k s hm : ℝ)/(1-ε)⌋₊ ≤ flatOrbitErrorMaximum C m n k s hsD ε ∧
      (flatOrbitErrorMaximum C m n k s hsD ε : ℝ) ≤
        rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε) := by
  constructor
  · apply (errorRankBudgetMaximum_bounds C m n k s hm hn hs hsD ε hε0 hε1).1.trans
    exact (flatOrbitErrorMaximum_isGreatest C m n k s hm hn hs hsD ε hε0 hε1).2
      (errorRankBudgetTargets_subset_flatOrbit C m n k s hs hsD ε
        (errorRankBudgetMaximum_attained C m n k s hm hn hs hsD ε hε0 hε1))
  · exact flatOrbitErrorTarget_le_budget C m n k s _ hm hn hs hsD ε hε1
      (flatOrbitErrorMaximum_attained C m n k s hm hn hs hsD ε hε0 hε1)

theorem flatOrbitErrorMaximum_ratio_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Tendsto (fun k => (flatOrbitErrorMaximum C m n k s hsD.le ε : ℝ)*(1-ε)/rankBudgetWidth m n k s)
      atTop (𝓝 1) := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  exact natural_error_target_ratio_limit (fun k => rankBudgetPacking m n k s hmp)
    (fun k => flatOrbitErrorMaximum C m n k s hsD.le ε) (fun k => rankBudgetWidth m n k s)
    (fun k => rankBudgetEta m n k s hsD.le) (1-ε) (by linarith)
    (fun k => rankBudgetWidth_pos m n k s hmp hn hs)
    (fun k => flatOrbitErrorMaximum_bounds C m n k s hmp hn hs hsD.le ε hε0 hε1)
    (rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD)
    (rankBudgetEta_limit m n s hs hsD.le) (rankBudgetWidth_atTop m n s hm hmn hs hsD)

/-- Fixed-error logarithmic target law for the flat spectrum. No assertion
about a nonuniform spectrum's fixed-error profile is used or concluded. -/
theorem flatOrbitErrorMaximum_log_limit (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Tendsto (fun k => Real.log (flatOrbitErrorMaximum C m n k s hsD.le ε : ℝ)-
      (Real.log (rankBudgetWidth m n k s)-Real.log (1-ε))) atTop (𝓝 0) := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  have hβ : (0 : ℝ) < 1-ε := by linarith
  have h := (flatOrbitErrorMaximum_ratio_limit C m n s hm hmn hs hsD ε hε0 hε1).log
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [] with k
  have hM : (0 : ℝ) < flatOrbitErrorMaximum C m n k s hsD.le ε := by
    exact_mod_cast (flatOrbitErrorMaximum_attained C m n k s hmp hn hs hsD.le ε hε0 hε1).1
  rw [Real.log_div (mul_pos hM hβ).ne' (rankBudgetWidth_pos m n k s hmp hn hs).ne',
    Real.log_mul hM.ne' hβ.ne']
  ring

end
end ExtractionSchur
