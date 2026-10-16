import RankSupport.TensorSupport

open scoped BigOperators
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport

theorem symmetric_rank_le_rankBudgetProjector_rank (D k s : ℕ) (hs : 1 ≤ s) :
    (symmetricProjector D k).rank ≤ (rankBudgetProjector D k s).rank := by
  change Module.finrank ℂ (LinearMap.range (symmetricProjector D k).mulVecLin) ≤ _
  rw [rankBudgetProjector_rank]
  exact Submodule.finrank_mono (symmetric_range_le_rankBudgetSpace D k s hs)

theorem rankBudgetProjector_rank_mono (D k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    (rankBudgetProjector D k s).rank ≤ (rankBudgetProjector D k t).rank := by
  rw [rankBudgetProjector_rank, rankBudgetProjector_rank]
  exact Submodule.finrank_mono (rankBudgetSpace_mono D k hst)

theorem rankBudgetProjector_rank_pos (D k s : ℕ) (hD : 0 < D) (hs : 1 ≤ s) :
    0 < (rankBudgetProjector D k s).rank := by
  apply lt_of_lt_of_le _ (symmetric_rank_le_rankBudgetProjector_rank D k s hs)
  rw [symmetricProjector_rank_choose]
  exact Nat.choose_pos (by omega)

theorem rankBudgetProjector_rank_le_dimension (D k s : ℕ) :
    (rankBudgetProjector D k s).rank ≤ D ^ k := by
  simpa only [Word, Fintype.card_fun, Fintype.card_fin] using
    Matrix.rank_le_card_width (rankBudgetProjector D k s)

theorem rankBudgetProjector_rank_one_choose (D k : ℕ) :
    (rankBudgetProjector D k 1).rank = (D + k - 1).choose k := by
  rw [rankBudgetProjector_one_eq_symmetricProjector, symmetricProjector_rank_choose]

theorem rankBudgetProjector_rank_eq_dimension (D k s : ℕ) (hs : D ≤ s) :
    (rankBudgetProjector D k s).rank = D ^ k := by
  rw [rankBudgetProjector_eq_one_of_dimension_le D k s hs, Matrix.rank_one]
  simp only [Word, Fintype.card_fun, Fintype.card_fin]

end ExtractionRankSupport
