import MinimaxProfile.Minimax
import MinimaxProfile.PackingLimit
import SpectralProtocol.GeneralPureGuarantee
import SymmetricSupport.PackingGrowth

open scoped BigOperators ComplexOrder
open Matrix Filter
namespace MinimaxProfile

abbrev UnitInput (D : ℕ) := {z : Fin D → ℂ // SymmetricSupport.IsUnitVector z}

noncomputable def pureMinimaxValue (m n k K : ℕ) : ℝ :=
  minimaxValue (fun z : UnitInput (m*n) => SpectralProtocol.purePowerInput m n k z.val) K

/-- Entire finite-target comparison for the true continuum of unknown pure
iid inputs, over actual completely-PPT Kraus protocols, with no average premise. -/
theorem pure_minimax_finite_bounds (m n k d K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hd : 0 < d) (hK : 0 < K)
    (hbudget : SpectralProtocol.pureSupportRank m n k ≤ (m^k/d)*(n^k/d)) :
    profile d K ≤ pureMinimaxValue m n k K ∧
    pureMinimaxValue m n k K ≤ min 1 (min ((m:ℝ)^k/K)
      (Real.sqrt (((m*n:ℕ):ℝ)^k / ((K:ℝ)^2*(SpectralProtocol.pureSupportRank m n k:ℝ))))) := by
  let X := fun z : UnitInput (m*n) => SpectralProtocol.purePowerInput m n k z.val
  obtain ⟨V,hV⟩ := common_support_profile_protocol (m^k) (n^k) d K hd hK
    (SpectralProtocol.purePowerProjection m n k)
    (SpectralProtocol.purePowerProjection_hermitian m n k)
    (SpectralProtocol.purePowerProjection_idempotent m n k)
    (by rwa [SpectralProtocol.purePowerProjection_rank m n k hm hn])
  have hlo : profile d K ∈ guaranteedValues X K := by
    refine ⟨V,fun z => ?_⟩
    exact (hV (X z) (SpectralProtocol.purePowerInput_density m n k z.val z.property)
      (SpectralProtocol.purePowerInput_supported m n k z.val)).ge
  have hupper (c : ℝ) (hc : c ∈ guaranteedValues X K) :
      c ≤ min 1 (min ((m:ℝ)^k/K)
        (Real.sqrt (((m*n:ℕ):ℝ)^k / ((K:ℝ)^2*(SpectralProtocol.pureSupportRank m n k:ℝ))))) := by
    obtain ⟨W,hW⟩ := hc
    exact SpectralProtocol.purePower_fidelity_guarantee_upper m n k K hm hn hK
      W.A W.complete W.ptPositive W.U c (fun z hz => hW ⟨z,hz⟩)
  exact ⟨le_csSup ⟨_,hupper⟩ hlo, csSup_le ⟨_,hlo⟩ hupper⟩

noncomputable def balancedWidth (m k : ℕ) : ℝ :=
  (m:ℝ)^k / Real.sqrt (SpectralProtocol.pureSupportRank m m k:ℝ)

theorem balancedWidth_pos (m k : ℕ) (hm : 0 < m) : 0 < balancedWidth m k := by
  have hr : (0:ℝ) < SpectralProtocol.pureSupportRank m m k := by
    exact_mod_cast SpectralProtocol.pureSupportRank_pos m m k hm hm
  exact div_pos (pow_pos (by exact_mod_cast hm) _) (Real.sqrt_pos.mpr hr)

theorem balancedWidth_budget (m k : ℕ) (hm : 0 < m) :
    (SpectralProtocol.pureSupportRank m m k:ℝ) * (balancedWidth m k)^2 =
      ((m^k:ℕ):ℝ) * ((m^k:ℕ):ℝ) := by
  have hr : (0:ℝ) < SpectralProtocol.pureSupportRank m m k := by
    exact_mod_cast SpectralProtocol.pureSupportRank_pos m m k hm hm
  rw [balancedWidth, div_pow, Real.sq_sqrt hr.le]
  push_cast
  field_simp
  <;> ring

theorem balancedWidth_le_local (m k : ℕ) (hm : 0 < m) : balancedWidth m k ≤ (m:ℝ)^k := by
  have hr : (1:ℝ) ≤ SpectralProtocol.pureSupportRank m m k := by
    exact_mod_cast SpectralProtocol.pureSupportRank_pos m m k hm hm
  have hs : 1 ≤ Real.sqrt (SpectralProtocol.pureSupportRank m m k:ℝ) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hr)
  unfold balancedWidth
  have hmp : (0:ℝ) ≤ (m:ℝ)^k := by positivity
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).mpr
  nlinarith

theorem balancedUpper_eq_profile (m k K : ℕ) (hm : 0 < m) (hK : 0 < K) :
    min 1 (min ((m:ℝ)^k/K)
      (Real.sqrt (((m*m:ℕ):ℝ)^k / ((K:ℝ)^2*(SpectralProtocol.pureSupportRank m m k:ℝ))))) =
      profile (balancedWidth m k) K := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : (((m*m:ℕ):ℝ)^k) = ((m:ℝ)^k)^2 := by push_cast; rw [mul_pow,pow_two]
  have hs : Real.sqrt (((m*m:ℕ):ℝ)^k / ((K:ℝ)^2*(SpectralProtocol.pureSupportRank m m k:ℝ))) =
      balancedWidth m k / K := by
    rw [hnum,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity),
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hKR.le]
    unfold balancedWidth
    ring
  rw [hs, min_eq_right (div_le_div_of_nonneg_right (balancedWidth_le_local m k hm) hKR.le)]
  rfl

/-- This finite result quantifies all requested targets and the entire pure-state
continuum. Every protocol, rank and average link is internal to the proof. -/
theorem balanced_pure_minimax_profile_bounds (m k K : ℕ) (hm : 0 < m) (hK : 0 < K) :
    let r := SpectralProtocol.pureSupportRank m m k
    let d := packingDimension (m^k) (m^k) r (pow_pos hm k)
      (by simpa only [mul_pow] using SpectralProtocol.pureSupportRank_le_dimension m m k hm hm)
    profile d K ≤ pureMinimaxValue m m k K ∧
      pureMinimaxValue m m k K ≤ profile (balancedWidth m k) K := by
  dsimp only
  have hrab : SpectralProtocol.pureSupportRank m m k ≤ m^k*m^k := by
    simpa only [mul_pow] using SpectralProtocol.pureSupportRank_le_dimension m m k hm hm
  have hprops := packingDimension_properties (pow_pos hm k) hrab
  have h := pure_minimax_finite_bounds m m k _ K hm hm hprops.1 hK hprops.2.2
  exact ⟨h.1, h.2.trans_eq (balancedUpper_eq_profile m k K hm hK)⟩

noncomputable def balancedPacking (m k : ℕ) (hm : 0 < m) : ℕ :=
  packingDimension (m^k) (m^k) (SpectralProtocol.pureSupportRank m m k) (pow_pos hm k)
    (by simpa only [mul_pow] using SpectralProtocol.pureSupportRank_le_dimension m m k hm hm)

theorem balancedWidth_atTop (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (balancedWidth m) atTop atTop := by
  have hmp : 0 < m := by omega
  have he (k : ℕ) : (SymmetricSupport.symmetricProjector (m*m) k).rank =
      SpectralProtocol.pureSupportRank m m k := by
    exact SymmetricSupport.symmetricProjector_rank_choose_complement (m*m) k (Nat.mul_pos hmp hmp)
  have h := SymmetricSupport.symmetricProjector_geometric_div_sqrt_rank_atTop
    (m*m) (Nat.mul_pos hmp hmp) (m:ℝ) (by exact_mod_cast hm : (1:ℝ) < m)
  change Tendsto (fun k => (m:ℝ)^k /
    Real.sqrt (SpectralProtocol.pureSupportRank m m k:ℝ)) atTop atTop
  simpa only [he] using h

theorem balancedWidth_div_local_tendsto_zero (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun k => balancedWidth m k / ((m^k:ℕ):ℝ)) atTop (nhds 0) := by
  have hmp : 0 < m := by omega
  have he (k : ℕ) : (SymmetricSupport.symmetricProjector (m*m) k).rank =
      SpectralProtocol.pureSupportRank m m k := by
    exact SymmetricSupport.symmetricProjector_rank_choose_complement (m*m) k (Nat.mul_pos hmp hmp)
  have hrank : Tendsto (fun k => (SpectralProtocol.pureSupportRank m m k:ℝ)) atTop atTop := by
    simpa only [he] using SymmetricSupport.symmetricProjector_rank_atTop (m*m) (by nlinarith)
  have hinv : Tendsto (fun k => 1 / Real.sqrt (SpectralProtocol.pureSupportRank m m k:ℝ))
      atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hrank)
  apply hinv.congr'
  apply Eventually.of_forall
  intro k
  unfold balancedWidth
  have hpow : (m:ℝ)^k ≠ 0 := ne_of_gt (pow_pos (by exact_mod_cast hmp) _)
  push_cast
  field_simp

/-- The optimum original integer packing has the exact pure-state continuous
width asymptotic, with no rank-growth hypothesis from the caller. -/
theorem balancedPacking_ratio_tendsto_one (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun k => (balancedPacking m k (by omega):ℝ) / balancedWidth m k)
      atTop (nhds 1) := by
  have hmp : 0 < m := by omega
  apply packing_ratio_tendsto (a := fun k => m^k) (b := fun k => m^k)
    (r := fun k => SpectralProtocol.pureSupportRank m m k)
    (w := balancedWidth m)
    (fun k => pow_pos hmp k) (fun k => pow_pos hmp k)
    (fun k => SpectralProtocol.pureSupportRank_pos m m k hmp hmp)
    (fun k => by simpa only [mul_pow] using
      SpectralProtocol.pureSupportRank_le_dimension m m k hmp hmp)
    (fun k => balancedWidth_pos m k hmp)
    (fun k => balancedWidth_budget m k hmp)
    (balancedWidth_atTop m hm)
    (balancedWidth_div_local_tendsto_zero m hm)
    (balancedWidth_div_local_tendsto_zero m hm)

/-- The balanced s=1 instance of the manuscript's uniform-in-every-target
minimax law, on the actual continuum of unknown pure iid states and genuine
fixed Kraus-PPT protocols. All support, averaging, rank and packing facts are
proved internally. -/
theorem balanced_pure_target_uniform_minimax (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun k => worstRelativeError (pureMinimaxValue m m k) (balancedWidth m k))
      atTop (nhds 0) := by
  have hmp : 0 < m := by omega
  let d := fun k => (balancedPacking m k hmp : ℝ)
  have hprops (k : ℕ) := packingDimension_properties (pow_pos hmp k)
    (show SpectralProtocol.pureSupportRank m m k ≤ m^k*m^k by
      simpa only [mul_pow] using SpectralProtocol.pureSupportRank_le_dimension m m k hmp hmp)
  have hfinite (k K : ℕ) (hK : 0 < K) :
      profile (d k) K ≤ pureMinimaxValue m m k K ∧
        pureMinimaxValue m m k K ≤ profile (balancedWidth m k) K := by
    exact balanced_pure_minimax_profile_bounds m k K hmp hK
  apply target_uniform_relative_limit (d := d) (w := balancedWidth m)
    (η := fun _ => 1) (F := pureMinimaxValue m m)
    (fun k => by dsimp only [d]; positivity)
    (fun k => ?_) (fun k => balancedWidth_pos m k hmp)
    (fun _ => le_rfl) (fun k K hK => (hfinite k K hK).1)
    (fun k K hK => by simpa only [one_mul] using (hfinite k K hK).2)
    (balancedPacking_ratio_tendsto_one m hm) tendsto_const_nhds
  exact feasible_dimension_real_bound
    (SpectralProtocol.pureSupportRank_pos m m k hmp hmp)
    (balancedWidth_pos m k hmp).le (balancedWidth_budget m k hmp) (hprops k).2.2

end MinimaxProfile
