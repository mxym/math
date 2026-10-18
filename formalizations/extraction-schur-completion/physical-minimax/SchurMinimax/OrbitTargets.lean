import SchurMinimax.TargetAsymptotics

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

def densityOrbitInput (D : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (U : OneCopyUnitary D) : RankBudgetInput D X.rank :=
  ⟨(U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ,
    (fixed_density_unitary_conjugate_density D X hX U).1,
    (fixed_density_unitary_conjugate_density D X hX U).2,
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)⟩

def orbitExactTargets (C : RankProtocolClass) (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : Set ℕ :=
  {K | 0 < K ∧ ∃ V : KrausPPTProtocol (m^k) (n^k) K, C.Allows V ∧
    ∀ U : OneCopyUnitary (m*n), V.fidelity
      (tensorInput m n k ((U : Matrix _ _ ℂ)*X*(U : Matrix _ _ ℂ)ᴴ))=1}

def orbitExactMaximum (C : RankProtocolClass) (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : ℕ := sSup (orbitExactTargets C m n k X)

theorem exactRankBudgetTargets_subset_orbit (C : RankProtocolClass) (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    exactRankBudgetTargets C m n k X.rank ⊆ orbitExactTargets C m n k X := by
  rintro K ⟨hK,V,hC,hV⟩
  exact ⟨hK,V,hC,fun U => hV (densityOrbitInput (m*n) X hX U)⟩

theorem orbitExactTarget_le_width (C : RankProtocolClass) (m n k K : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hK : K ∈ orbitExactTargets C m n k X) : (K : ℝ) ≤ rankBudgetWidth m n k X.rank := by
  obtain ⟨hK,V,hC,hV⟩ := hK
  have h := exact_fixedOrbit_physical_budget m n k K hm hn hK X hX V hV
  apply le_min (by exact_mod_cast h.2)
  apply Real.le_sqrt_of_sq_le
  have hr := rankBudget_rank_pos m n k X.rank hm hn (SpectralProtocol.density_rank_pos X hX.2)
  have hrR : (0 : ℝ) < (rankBudgetProjector (m*n) k X.rank).rank := by exact_mod_cast hr
  apply (le_div_iff₀ hrR).mpr
  nlinarith [h.1]

theorem orbitExactTargets_nonempty_bdd (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    (orbitExactTargets C m n k X).Nonempty ∧ BddAbove (orbitExactTargets C m n k X) := by
  have hs := SpectralProtocol.density_rank_pos X hX.2
  have hsD : X.rank ≤ m*n := by simpa using Matrix.rank_le_card_width X
  constructor
  · exact (exactRankBudgetTargets_nonempty_bdd C m n k X.rank hm hn hs hsD).1.mono
      (exactRankBudgetTargets_subset_orbit C m n k X hX)
  · exact ⟨⌊rankBudgetWidth m n k X.rank⌋₊,fun K hK => Nat.le_floor
      (orbitExactTarget_le_width C m n k K hm hn X hX hK)⟩

theorem orbitExactMaximum_attained (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    orbitExactMaximum C m n k X ∈ orbitExactTargets C m n k X :=
  Nat.sSup_mem (orbitExactTargets_nonempty_bdd C m n k hm hn X hX).1
    (orbitExactTargets_nonempty_bdd C m n k hm hn X hX).2

theorem orbitExactMaximum_bounds (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    rankBudgetPacking m n k X.rank hm ≤ orbitExactMaximum C m n k X ∧
      orbitExactMaximum C m n k X ≤ ⌊rankBudgetWidth m n k X.rank⌋₊ := by
  have hs := SpectralProtocol.density_rank_pos X hX.2
  constructor
  · exact le_csSup (orbitExactTargets_nonempty_bdd C m n k hm hn X hX).2
      (exactRankBudgetTargets_subset_orbit C m n k X hX
        (le_packing_mem_exactTargets C m n k X.rank _ hm hn hs
          (rankBudgetPacking_properties m n k X.rank hm hn hs).1 le_rfl))
  · exact Nat.le_floor (orbitExactTarget_le_width C m n k _ hm hn X hX
      (orbitExactMaximum_attained C m n k hm hn X hX))

theorem orbitExactMaximum_isGreatest (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    IsGreatest (orbitExactTargets C m n k X) (orbitExactMaximum C m n k X) :=
  ⟨orbitExactMaximum_attained C m n k hm hn X hX,
    fun K hK => le_csSup (orbitExactTargets_nonempty_bdd C m n k hm hn X hX).2 hK⟩

/-- Any known positive rank-s spectrum, with unknown global orientation,
has the same exact-target logarithmic correction as the full rank budget. -/
theorem orbitExactMaximum_log_correction_limit (C : RankProtocolClass) (m n : ℕ)
    (hm : 0 < m) (hmn : m ≤ n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hsD : X.rank < m*n) (hregime : n ≤ m*X.rank) :
    Tendsto (fun k => Real.log (orbitExactMaximum C m n k X : ℝ)-rankBudgetLogScale m n k X.rank)
      atTop (𝓝 0) := by
  have hn : 0 < n := hm.trans_le hmn
  have hs := SpectralProtocol.density_rank_pos X hX.2
  have hratio := natural_packing_width_ratio_limit (fun k => rankBudgetPacking m n k X.rank hm)
    (fun k => orbitExactMaximum C m n k X) (fun k => rankBudgetWidth m n k X.rank)
    (fun k => rankBudgetWidth_pos m n k X.rank hm hn hs)
    (fun k => ⟨(orbitExactMaximum_bounds C m n k hm hn X hX).1,
      orbitExactTarget_le_width C m n k _ hm hn X hX (orbitExactMaximum_attained C m n k hm hn X hX)⟩)
    (rankBudgetPacking_ratio_limit m n X.rank hm hmn hs hsD)
  have hlog := log_nat_ratio_limit _ _
    (fun k => (orbitExactMaximum_attained C m n k hm hn X hX).1)
    (fun k => rankBudgetWidth_pos m n k X.rank hm hn hs) hratio
  have h := hlog.add (rankBudget_log_width_correction_limit m n X.rank hm hmn hs hsD hregime)
  simpa only [sub_add_sub_cancel, add_zero] using h

theorem orbitExactMaximum_eventually_local (C : RankProtocolClass) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hregime : m*X.rank < n) : ∀ᶠ k : ℕ in atTop, orbitExactMaximum C m n k X=m^k := by
  filter_upwards [rankBudgetPacking_eventually_local m n X.rank hm
    (SpectralProtocol.density_rank_pos X hX.2) hregime] with k hk
  have hb := orbitExactMaximum_bounds C m n k hm hn X hX
  apply le_antisymm
  · have hw : ⌊rankBudgetWidth m n k X.rank⌋₊=m^k := by
      rw [hk.2]
      simp only [← Nat.cast_pow,Nat.floor_natCast]
    exact hb.2.trans_eq hw
  · rw [← hk.1]
    exact hb.1

end
end ExtractionSchur
