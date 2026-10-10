import ErdosSimilarityGrowingGaps.Corollary
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace ErdosSimilarityGrowingGaps
open Filter Topology

/-- The positive input sequence represented by a logarithmic scale. -/
noncomputable def input (Z : LogScale) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-Z.z n)

theorem input_eq_rpow (Z : LogScale) (n : ℕ) :
    input Z n = (2 : ℝ) ^ (-Z.z n) := rfl

theorem input_pos (Z : LogScale) (n : ℕ) : 0 < input Z n := by
  unfold input
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem input_tendsto_zero (Z : LogScale) :
    Tendsto (input Z) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => -Z.z n) atTop atBot :=
    tendsto_neg_atTop_atBot.comp Z.tendsto_atTop
  convert (tendsto_rpow_atBot_of_base_gt_one (2 : ℝ) (by norm_num)).comp hz using 1
  ext n
  rfl

theorem input_strictAnti (Z : LogScale) : StrictAnti (input Z) := by
  intro i j hij
  unfold input
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  exact neg_lt_neg (Z.strictMono hij)

theorem input_logb (Z : LogScale) (n : ℕ) :
    -Real.logb 2 (input Z n) = Z.z n := by
  unfold input
  rw [Real.logb_rpow (by norm_num) (by norm_num)]
  ring

end ErdosSimilarityGrowingGaps
