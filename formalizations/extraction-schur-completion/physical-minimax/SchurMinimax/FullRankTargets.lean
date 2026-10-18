import SchurMinimax.FlatErrorTargets

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rankBudget_full_rank_width_eta (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    rankBudgetWidth m n k (m*n)=1 ∧ rankBudgetEta m n k (m*n) le_rfl=1 := by
  have hD : (0 : ℝ) < (m*n : ℕ) := by exact_mod_cast Nat.mul_pos hm hn
  have hpow : (0 : ℝ) < ((m*n : ℕ) : ℝ)^k := pow_pos hD k
  have hr : ((rankBudgetProjector (m*n) k (m*n)).rank : ℝ)=((m*n : ℕ) : ℝ)^k := by
    rw [rankBudgetProjector_rank_eq_dimension (m*n) k (m*n) le_rfl, Nat.cast_pow]
  constructor
  · rw [rankBudgetWidth,rankBudgetCollisionWidth,hr,div_self hpow.ne',Real.sqrt_one]
    exact min_eq_right (one_le_pow₀ (by exact_mod_cast hm : (1 : ℝ) ≤ m))
  · rw [rankBudgetEta,hr,flatHaarAverage_full_rank_purity,mul_inv_cancel₀ hpow.ne',Real.sqrt_one]

theorem rankBudget_full_rank_packing (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    rankBudgetPacking m n k (m*n) hm=1 := by
  have h := rankBudgetPacking_properties m n k (m*n) hm hn (Nat.mul_pos hm hn)
  have hu : (rankBudgetPacking m n k (m*n) hm : ℝ) ≤ 1 := by
    simpa only [(rankBudget_full_rank_width_eta m n k hm hn).1] using h.2.1
  have huN : rankBudgetPacking m n k (m*n) hm ≤ 1 := by exact_mod_cast hu
  omega

theorem exactRankBudgetMaximum_full_rank (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n) : exactRankBudgetMaximum C m n k (m*n)=1 := by
  have h := exactRankBudgetMaximum_bounds C m n k (m*n) hm hn (Nat.mul_pos hm hn) le_rfl
  rw [rankBudget_full_rank_packing m n k hm hn,
    (rankBudget_full_rank_width_eta m n k hm hn).1] at h
  norm_num at h
  omega

theorem errorRankBudgetMaximum_full_rank (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    errorRankBudgetMaximum C m n k (m*n) ε=⌊1/(1-ε)⌋₊ := by
  have h := errorRankBudgetMaximum_bounds C m n k (m*n) hm hn (Nat.mul_pos hm hn) le_rfl ε hε0 hε1
  rw [rankBudget_full_rank_packing m n k hm hn,
    (rankBudget_full_rank_width_eta m n k hm hn).1,
    (rankBudget_full_rank_width_eta m n k hm hn).2] at h
  norm_num only [Nat.cast_one,one_mul] at h
  exact le_antisymm (Nat.le_floor h.2) h.1

theorem orbitExactMaximum_full_rank (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hr : X.rank=m*n) : orbitExactMaximum C m n k X=1 := by
  have h := orbitExactMaximum_bounds C m n k hm hn X hX
  rw [hr,rankBudget_full_rank_packing m n k hm hn,
    (rankBudget_full_rank_width_eta m n k hm hn).1] at h
  norm_num at h
  omega

theorem flatOrbit_full_rank_minimax (C : RankProtocolClass) (m n k K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hK : 0 < K) :
    flatOrbitPhysicalMinimax C m n k (m*n) le_rfl K=1/(K : ℝ) := by
  have h := flatOrbit_minimax_profile_bounds C m n k (m*n) K hm hn (Nat.mul_pos hm hn) le_rfl hK
  rw [rankBudget_full_rank_packing m n k hm hn,
    (rankBudget_full_rank_width_eta m n k hm hn).1,
    (rankBudget_full_rank_width_eta m n k hm hn).2] at h
  have hp : profile (1 : ℝ) K=1/(K : ℝ) := by
    unfold profile
    apply min_eq_right
    apply (div_le_one (by exact_mod_cast hK : (0 : ℝ) < K)).mpr
    exact_mod_cast hK
  simp only [one_mul,Nat.cast_one] at h
  simpa only [hp] using le_antisymm h.2 h.1

theorem flatOrbitErrorMaximum_full_rank (C : RankProtocolClass) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    flatOrbitErrorMaximum C m n k (m*n) le_rfl ε=⌊1/(1-ε)⌋₊ := by
  have h := flatOrbitErrorMaximum_bounds C m n k (m*n) hm hn (Nat.mul_pos hm hn) le_rfl ε hε0 hε1
  rw [rankBudget_full_rank_packing m n k hm hn,
    (rankBudget_full_rank_width_eta m n k hm hn).1,
    (rankBudget_full_rank_width_eta m n k hm hn).2] at h
  norm_num only [Nat.cast_one,one_mul] at h
  exact le_antisymm (Nat.le_floor h.2) h.1

end
end ExtractionSchur
