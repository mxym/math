import SchurMinimax.OrbitTargets

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

def flatOrbitPhysicalMinimax (C : RankProtocolClass) (m n k s : ℕ) (hsD : s ≤ m*n) (K : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ U : OneCopyUnitary (m*n), c ≤ V.fidelity (tensorInput m n k
      ((U : Matrix _ _ ℂ)*flatCoordinateDensity (m*n) s hsD*(U : Matrix _ _ ℂ)ᴴ))}

theorem orbit_guarantee_le_haar (m n k K : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ)
    (V : KrausPPTProtocol (m^k) (n^k) K) (c : ℝ)
    (hc : ∀ U : OneCopyUnitary (m*n), c ≤ V.fidelity
      (tensorInput m n k ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ))) :
    c ≤ V.fidelity (SpectralProtocol.bipartitePowerTransport m n k (haarOrbitAverage (m*n) k X)) := by
  let L := (SpectralProtocol.bipartitePowerTransport m n k).toLinearMap.toContinuousLinearMap
  have hint := integrable_orbitTensor (m*n) k X
  have htrans : SpectralProtocol.bipartitePowerTransport m n k (haarOrbitAverage (m*n) k X) =
      ∫ U : OneCopyUnitary (m*n), tensorInput m n k
        ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ) ∂unitaryHaar (m*n) :=
    (L.integral_comp_comm hint).symm
  have hi := L.integrable_comp hint
  have hfid := (fidelityLinear V).toContinuousLinearMap.integral_comp_comm hi
  have hfid' : (∫ U : OneCopyUnitary (m*n), V.fidelity (tensorInput m n k
      ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ)) ∂unitaryHaar (m*n)) =
      V.fidelity (SpectralProtocol.bipartitePowerTransport m n k (haarOrbitAverage (m*n) k X)) := by
    rw [htrans]
    exact hfid
  have h := integral_mono (integrable_const c)
    ((fidelityLinear V).toContinuousLinearMap.integrable_comp hi) hc
  simp only [integral_const,probReal_univ,one_smul] at h
  have hh : c ≤ ∫ U : OneCopyUnitary (m*n), V.fidelity (tensorInput m n k
      ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ)) ∂unitaryHaar (m*n) := by exact h
  exact hh.trans_eq hfid'

theorem physicalHaarAverage_fidelity_upper_profile (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K)
    (V : KrausPPTProtocol (m^k) (n^k) K) :
    V.fidelity (physicalHaarAverage m n k s hsD) ≤
      profile (rankBudgetEta m n k s hsD*rankBudgetWidth m n k s) K := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have hh := ExtractionLocalCap.kraus_target_overlap_full_envelope V.A V.complete V.ptPositive
    (physicalHaarAverage m n k s hsD) (physicalHaarAverage_density m n k s hs hsD) V.U
  have hupper : V.fidelity (physicalHaarAverage m n k s hsD) ≤ min 1 (min ((m : ℝ)^k/K)
      (Real.sqrt ((flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
        (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2)))) := by
    simpa only [KrausPPTProtocol.fidelity,overlap,Fintype.card_fin,physicalHaarAverage_purity,
      Nat.cast_pow,Nat.cast_mul,mul_pow] using hh
  apply hupper.trans
  have hη := rankBudgetEta_ge_one m n k s hs hsD
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hΩ := (flatHaarAverage_density (m*n) s k hs hsD).1
  have hp : 0 ≤ (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re := by
    have hΩ2 : (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).PosSemidef := by
      simpa only [hΩ.isHermitian.eq] using Matrix.posSemidef_self_mul_conjTranspose (flatHaarAverage (m*n) s k hsD)
    exact (RCLike.nonneg_iff.mp hΩ2.trace_nonneg).1
  have hsqrt : Real.sqrt ((flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
      (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2)) =
      (rankBudgetEta m n k s hsD*rankBudgetCollisionWidth m n k s)/(K : ℝ) := by
    rw [rankBudget_eta_collision_identity m n k s hm hn hs hsD]
    have he : (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
        (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2) =
        ((((m*n : ℕ) : ℝ)^k)*
          (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re)/(K : ℝ)^2 := by ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hKR.le]
  rw [hsqrt]
  apply le_min (min_le_left _ _)
  by_cases ha : (m : ℝ)^k ≤ rankBudgetCollisionWidth m n k s
  · rw [rankBudgetWidth, min_eq_left ha]
    apply ((min_le_right _ _).trans (min_le_left _ _)).trans
    apply div_le_div_of_nonneg_right _ hKR.le
    have hp : 0 ≤ (m : ℝ)^k := by positivity
    nlinarith
  · rw [rankBudgetWidth, min_eq_right (le_of_not_ge ha)]
    exact (min_le_right _ _).trans (min_le_right _ _)

theorem flatOrbit_minimax_profile_bounds (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K) :
    profile (rankBudgetPacking m n k s hm) K ≤ flatOrbitPhysicalMinimax C m n k s hsD K ∧
      flatOrbitPhysicalMinimax C m n k s hsD K ≤
        profile (rankBudgetEta m n k s hsD*rankBudgetWidth m n k s) K := by
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have hP := rankBudgetProjection_properties m n k s
  obtain ⟨V,hLocal,hV⟩ := common_support_local_profile (m^k) (n^k)
    (rankBudgetPacking m n k s hm) K hprops.1 hK
    (rankBudgetProjection m n k s) hP.1 hP.2.1 (by rw [hP.2.2];exact hprops.2.2)
  let S : Set ℝ := {c | ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ U : OneCopyUnitary (m*n), c ≤ V.fidelity (tensorInput m n k
      ((U : Matrix _ _ ℂ)*flatCoordinateDensity (m*n) s hsD*(U : Matrix _ _ ℂ)ᴴ))}
  have hlo : profile (rankBudgetPacking m n k s hm) K ∈ S := by
    refine ⟨V,C.allows_productLocal V hLocal,fun U => ?_⟩
    let X := rankBudgetOrbitInput (m*n) s hs hsD U
    exact (hV _ (tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩)
      (tensorInput_rankBudget_supported m n k s X)).ge
  have hup (c : ℝ) (hc : c ∈ S) :
      c ≤ profile (rankBudgetEta m n k s hsD*rankBudgetWidth m n k s) K := by
    obtain ⟨W,hCW,hW⟩ := hc
    exact (orbit_guarantee_le_haar m n k K (flatCoordinateDensity (m*n) s hsD) W c hW).trans
      (physicalHaarAverage_fidelity_upper_profile m n k s K hm hn hs hsD hK W)
  exact ⟨le_csSup ⟨_,hup⟩ hlo,csSup_le ⟨_,hlo⟩ hup⟩

/-- The flat known spectrum with unknown orientation alone has the entire
target-uniform relative minimax profile for all actual physical classes. -/
theorem flatOrbit_target_uniform_minimax (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => worstRelativeError (flatOrbitPhysicalMinimax C m n k s hsD.le)
      (rankBudgetWidth m n k s)) atTop (𝓝 0) := by
  have hmp : 0 < m := by omega
  have hn : 0 < n := hmp.trans_le hmn
  apply target_uniform_relative_limit
    (d := fun k => (rankBudgetPacking m n k s hmp : ℝ))
    (w := fun k => rankBudgetWidth m n k s) (η := fun k => rankBudgetEta m n k s hsD.le)
    (F := fun k => flatOrbitPhysicalMinimax C m n k s hsD.le)
    (fun k => by positivity) (fun k => (rankBudgetPacking_properties m n k s hmp hn hs).2.1)
    (fun k => rankBudgetWidth_pos m n k s hmp hn hs)
    (fun k => rankBudgetEta_ge_one m n k s hs hsD.le)
  · intro k K hK
    exact (flatOrbit_minimax_profile_bounds C m n k s K hmp hn hs hsD.le hK).1
  · intro k K hK
    exact (flatOrbit_minimax_profile_bounds C m n k s K hmp hn hs hsD.le hK).2
  · exact rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD
  · exact rankBudgetEta_limit m n s hs hsD.le

theorem flatOrbit_target_uniform_relative_error (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |flatOrbitPhysicalMinimax C m n k s hsD.le K/profile (rankBudgetWidth m n k s) K-1| < ε := by
  have hmp : 0 < m := by omega
  have hnp : 0 < n := hmp.trans_le hmn
  have hratio := rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD
  have heta := rankBudgetEta_limit m n s hs hsD.le
  have herr := (Tendsto.const_sub 1 hratio).max (heta.sub_const 1)
  have herr0 : Tendsto (fun k => max
      (1-(rankBudgetPacking m n k s hmp : ℝ)/rankBudgetWidth m n k s)
      (rankBudgetEta m n k s hsD.le-1)) atTop (𝓝 0) := by simpa using herr
  filter_upwards [(tendsto_order.1 herr0).2 ε hε] with k hk
  intro K hK
  have hprops := rankBudgetPacking_properties m n k s hmp hnp hs
  have hfinite := flatOrbit_minimax_profile_bounds C m n k s K hmp hnp hs hsD.le hK
  exact (relative_profile_bound (by positivity) hprops.2.1
    (rankBudgetWidth_pos m n k s hmp hnp hs) (rankBudgetEta_ge_one m n k s hs hsD.le)
    (by exact_mod_cast hK) hfinite.1 hfinite.2).trans_lt hk

end
end ExtractionSchur
