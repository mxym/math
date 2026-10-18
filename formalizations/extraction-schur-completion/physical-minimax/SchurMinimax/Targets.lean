import SchurMinimax.FullRank
import SpectralProtocol.ProjectionState
import SpectralProtocol.PureBell
import SpectralProtocol.FixedOrbitBell
import Mathlib.Order.Lattice.Nat

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

def exactRankBudgetTargets (C : RankProtocolClass) (m n k s : ℕ) : Set ℕ :=
  {K | 0 < K ∧ ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ X : RankBudgetInput (m*n) s, V.fidelity (tensorInput m n k X.val)=1}

def errorRankBudgetTargets (C : RankProtocolClass) (m n k s : ℕ) (ε : ℝ) : Set ℕ :=
  {K | 0 < K ∧ ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ X : RankBudgetInput (m*n) s, 1-ε ≤ V.fidelity (tensorInput m n k X.val)}

def exactRankBudgetMaximum (C : RankProtocolClass) (m n k s : ℕ) : ℕ :=
  sSup (exactRankBudgetTargets C m n k s)

def errorRankBudgetMaximum (C : RankProtocolClass) (m n k s : ℕ) (ε : ℝ) : ℕ :=
  sSup (errorRankBudgetTargets C m n k s ε)

theorem exact_fixedOrbit_effect_fixes_rankBudget (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (M : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)
    (hM : (1-M).PosSemidef)
    (hfit : ∀ U : OneCopyUnitary (m*n),
      (M*tensorInput m n k ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ)).trace.re=1) :
    M*rankBudgetProjection m n k X.rank=rankBudgetProjection m n k X.rank := by
  let T := SpectralProtocol.bipartitePowerTransport m n k
  let M' := T.symm M
  have hM' : (1-M').PosSemidef := by
    have h := hM.submatrix (SpectralProtocol.bipartitePowerCoordinates m n k)
    simp only [M', T, SpectralProtocol.bipartitePowerTransport, Matrix.symm_reindexAlgEquiv]
    change (1-M.submatrix (SpectralProtocol.bipartitePowerCoordinates m n k)
      (SpectralProtocol.bipartitePowerCoordinates m n k)).PosSemidef
    simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using h
  have hf' (U : OneCopyUnitary (m*n)) :
      (M'*tensorMatrix ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ) k).trace.re=1 := by
    have he : (M'*tensorMatrix ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ) k).trace =
        (M*tensorInput m n k ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ)).trace := by
      rw [← SpectralProtocol.reindex_trace (SpectralProtocol.bipartitePowerCoordinates m n k)]
      change (T (M'*tensorMatrix _ k)).trace=_
      rw [map_mul]
      simp only [M', AlgEquiv.apply_symm_apply, tensorInput, T]
    rw [he]
    exact hfit U
  have h := exact_fixed_density_orbit_effect_mul_rankBudgetProjector (m*n) k X hX M' hM' hf'
  have hh := congrArg T h
  simpa only [map_mul, M', AlgEquiv.apply_symm_apply, rankBudgetProjection, T] using hh

theorem exact_fixedOrbit_physical_budget (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n) (hK : 0 < K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (V : KrausPPTProtocol (m^k) (n^k) K)
    (hfit : ∀ U : OneCopyUnitary (m*n), V.fidelity
      (tensorInput m n k ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ))=1) :
    ((rankBudgetProjector (m*n) k X.rank).rank : ℝ)*(K : ℝ)^2 ≤
      ((m*n : ℕ) : ℝ)^k ∧ K ≤ m^k := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let M := SpectralProtocol.preprocessedEffect V.A V.U
  have hM := SpectralProtocol.one_sub_preprocessedEffect_posSemidef V.A V.complete V.ptPositive V.U
  have hfix : M*rankBudgetProjection m n k X.rank=rankBudgetProjection m n k X.rank := by
    apply exact_fixedOrbit_effect_fixes_rankBudget m n k X hX M hM
    intro U
    rw [← SpectralProtocol.preprocessedEffect_pairing]
    exact hfit U
  have hP := rankBudgetProjection_properties m n k X.rank
  have hr : 0 < (rankBudgetProjection m n k X.rank).rank := by
    rw [hP.2.2]
    exact rankBudgetProjector_rank_pos (m*n) k X.rank (Nat.mul_pos hm hn)
      (SpectralProtocol.density_rank_pos X hX.2)
  have hall (Y : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)
      (hY : APPT.Quantum.IsDensity Y) (hPY : rankBudgetProjection m n k X.rank*Y*
        rankBudgetProjection m n k X.rank=Y) : V.fidelity Y=1 := by
    rw [KrausPPTProtocol.fidelity, overlap, SpectralProtocol.preprocessedEffect_pairing]
    have he : M*Y=Y := by
      calc
        _ = M*(rankBudgetProjection m n k X.rank*Y*rankBudgetProjection m n k X.rank) := by rw [hPY]
        _ = _ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix, hPY]
    change (M*Y).trace.re=1
    rw [he,hY.2,Complex.one_re]
  have hbudget := SpectralProtocol.exact_common_support_dimension_budget
    (rankBudgetProjection m n k X.rank) hP.1 hP.2.1 hr V.A V.complete V.ptPositive V.U hall
  constructor
  · simpa only [hP.2.2, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, mul_pow] using hbudget
  · have hXi := tensorInput_density m n k X hX
    have hu := ExtractionLocalCap.kraus_target_overlap_full_envelope V.A V.complete V.ptPositive
      (tensorInput m n k X) hXi V.U
    simp only [Fintype.card_fin] at hu
    have hfirst : V.fidelity (tensorInput m n k X)=1 := by
      simpa only [Matrix.UnitaryGroup.one_val, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hfit 1
    have hc : 1 ≤ ((m^k : ℕ) : ℝ)/(K : ℝ) :=
      hfirst ▸ hu.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)).mp hc
    have hkR : (K : ℝ) ≤ ((m^k : ℕ) : ℝ) := by simpa only [one_mul] using hh
    exact_mod_cast hkR

theorem exactRankBudgetTarget_le_width (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n)
    (hK : K ∈ exactRankBudgetTargets C m n k s) : (K : ℝ) ≤ rankBudgetWidth m n k s := by
  obtain ⟨hK,V,hC,hV⟩ := hK
  have hf (U : OneCopyUnitary (m*n)) := hV (rankBudgetOrbitInput (m*n) s hs hsD U)
  have h := exact_fixedOrbit_physical_budget m n k K hm hn hK
    (flatCoordinateDensity (m*n) s hsD) (flatCoordinateDensity_density (m*n) s hs hsD) V hf
  rw [flatCoordinateDensity_rank (m*n) s hs hsD] at h
  apply le_min (by exact_mod_cast h.2)
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by exact_mod_cast rankBudget_rank_pos m n k s hm hn hs :
    (0 : ℝ) < (rankBudgetProjector (m*n) k s).rank)).mpr
  nlinarith [h.1]

theorem le_packing_mem_exactTargets (C : RankProtocolClass) (m n k s K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hK : 0 < K)
    (hKd : K ≤ rankBudgetPacking m n k s hm) : K ∈ exactRankBudgetTargets C m n k s := by
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have hP := rankBudgetProjection_properties m n k s
  obtain ⟨V,hLocal,hV⟩ := common_support_local_profile (m^k) (n^k)
    (rankBudgetPacking m n k s hm) K hprops.1 hK
    (rankBudgetProjection m n k s) hP.1 hP.2.1 (by rw [hP.2.2];exact hprops.2.2)
  refine ⟨hK,V,C.allows_productLocal V hLocal,fun X => ?_⟩
  rw [hV _ (tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩)
    (tensorInput_rankBudget_supported m n k s X)]
  unfold profile
  exact min_eq_left ((one_le_div (by exact_mod_cast hK : (0 : ℝ) < K)).mpr (by exact_mod_cast hKd))

theorem exactRankBudgetTargets_nonempty_bdd (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) :
    (exactRankBudgetTargets C m n k s).Nonempty ∧ BddAbove (exactRankBudgetTargets C m n k s) := by
  constructor
  · exact ⟨1,le_packing_mem_exactTargets C m n k s 1 hm hn hs (by omega)
      (rankBudgetPacking_properties m n k s hm hn hs).1⟩
  · refine ⟨⌊rankBudgetWidth m n k s⌋₊,fun K hK => ?_⟩
    exact Nat.le_floor (exactRankBudgetTarget_le_width C m n k s K hm hn hs hsD hK)

theorem exactRankBudgetMaximum_attained (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) :
    exactRankBudgetMaximum C m n k s ∈ exactRankBudgetTargets C m n k s :=
  Nat.sSup_mem (exactRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD).1
    (exactRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD).2

theorem exactRankBudgetMaximum_bounds (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) :
    rankBudgetPacking m n k s hm ≤ exactRankBudgetMaximum C m n k s ∧
      exactRankBudgetMaximum C m n k s ≤ ⌊rankBudgetWidth m n k s⌋₊ := by
  constructor
  · exact le_csSup (exactRankBudgetTargets_nonempty_bdd C m n k s hm hn hs hsD).2
      (le_packing_mem_exactTargets C m n k s _ hm hn hs
        (rankBudgetPacking_properties m n k s hm hn hs).1 le_rfl)
  · exact Nat.le_floor (exactRankBudgetTarget_le_width C m n k s _ hm hn hs hsD
      (exactRankBudgetMaximum_attained C m n k s hm hn hs hsD))

end
end ExtractionSchur
