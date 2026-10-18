import SchurMinimax.Targets

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rankBudget_protocol_guarantee_le_value (C : RankProtocolClass) (m n k s K : ℕ)
    (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K)
    (V : KrausPPTProtocol (m^k) (n^k) K) (hC : C.Allows V) (c : ℝ)
    (hc : ∀ X : RankBudgetInput (m*n) s, c ≤ V.fidelity (tensorInput m n k X.val)) :
    c ≤ rankBudgetPhysicalMinimax C m n k s K := by
  unfold rankBudgetPhysicalMinimax rankBudgetClassMinimax
  refine le_csSup ?_ ?_
  swap
  · exact ⟨V,hC,hc⟩
  refine ⟨1,?_⟩
  rintro b ⟨W,hCW,hW⟩
  let X := rankBudgetOrbitInput (m*n) s hs hsD 1
  have hX := tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have h := ExtractionLocalCap.kraus_target_overlap_full_envelope W.A W.complete W.ptPositive
    (tensorInput m n k X.val) hX W.U
  exact (hW X).trans (h.trans (min_le_left _ _))

theorem errorRankBudgetTarget_le_budget (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε : ε < 1) (hK : K ∈ errorRankBudgetTargets C m n k s ε) :
    (K : ℝ) ≤ rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε) := by
  obtain ⟨hK,V,hC,hV⟩ := hK
  have h := rankBudget_protocol_guarantee_le_value C m n k s K hs hsD hK V hC (1-ε) hV
  have hupper := (rankBudget_class_profile_bounds m n k s K hm hn hs hsD hK
    C.Allows C.allows_productLocal).2
  have hh := h.trans (hupper.trans (min_le_right _ _))
  have hmul := (le_div_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)).mp hh
  exact (le_div_iff₀ (by linarith : (0 : ℝ) < 1-ε)).mpr (by nlinarith)

theorem le_packing_threshold_mem_errorTargets (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hK : 0 < K) (hKd : (K : ℝ) ≤ (rankBudgetPacking m n k s hm : ℝ)/(1-ε)) :
    K ∈ errorRankBudgetTargets C m n k s ε := by
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have hP := rankBudgetProjection_properties m n k s
  obtain ⟨V,hLocal,hV⟩ := common_support_local_profile (m^k) (n^k)
    (rankBudgetPacking m n k s hm) K hprops.1 hK
    (rankBudgetProjection m n k s) hP.1 hP.2.1 (by rw [hP.2.2];exact hprops.2.2)
  refine ⟨hK,V,C.allows_productLocal V hLocal,fun X => ?_⟩
  rw [hV _ (tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩)
    (tensorInput_rankBudget_supported m n k s X)]
  apply le_min (by linarith)
  apply (le_div_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)).mpr
  have hh := (le_div_iff₀ (by linarith : (0 : ℝ) < 1-ε)).mp hKd
  nlinarith

theorem errorRankBudgetTargets_nonempty_bdd (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (errorRankBudgetTargets C m n k s ε).Nonempty ∧ BddAbove (errorRankBudgetTargets C m n k s ε) := by
  constructor
  · obtain ⟨K,hK,V,hC,hV⟩ := (exactRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD).1
    exact ⟨K,hK,V,hC,fun X => by rw [hV X];linarith⟩
  · refine ⟨⌊rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε)⌋₊,fun K hK => ?_⟩
    exact Nat.le_floor (errorRankBudgetTarget_le_budget C m n k s K hm hn hs hsD ε hε1 hK)

theorem errorRankBudgetMaximum_attained (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    errorRankBudgetMaximum C m n k s ε ∈ errorRankBudgetTargets C m n k s ε :=
  Nat.sSup_mem (errorRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).1
    (errorRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).2

theorem errorRankBudgetMaximum_bounds (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ⌊(rankBudgetPacking m n k s hm : ℝ)/(1-ε)⌋₊ ≤ errorRankBudgetMaximum C m n k s ε ∧
      (errorRankBudgetMaximum C m n k s ε : ℝ) ≤
        rankBudgetEta m n k s hsD*rankBudgetWidth m n k s/(1-ε) := by
  have hβ : (0 : ℝ) < 1-ε := by linarith
  have hd : (1 : ℝ) ≤ rankBudgetPacking m n k s hm := by
    exact_mod_cast (rankBudgetPacking_properties m n k s hm hn hs).1
  constructor
  · apply le_csSup (errorRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD ε hε0 hε1).2
    apply le_packing_threshold_mem_errorTargets C m n k s _ hm hn hs ε hε0 hε1
    · apply Nat.floor_pos.mpr
      apply (le_div_iff₀ hβ).mpr
      nlinarith
    · exact Nat.floor_le (by positivity)
  · exact errorRankBudgetTarget_le_budget C m n k s _ hm hn hs hsD ε hε1
      (errorRankBudgetMaximum_attained C m n k s hm hn hs hsD ε hε0 hε1)

end
end ExtractionSchur
