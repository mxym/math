import APPTReview.PlateauRankMaximum
import APPTReview.PrefixCut

open scoped BigOperators
namespace APPTReview

theorem cut_constraint_cannot_be_dropped :
    spectralSquares (cutPair 1 1 (![1,0] : Fin 2 → ℝ) ![1/2,1/2])=5/8 ∧
    spectralSquares (![1/2,1/2] : Fin 2 → ℝ)=1/2 ∧
    (5/8:ℝ) < spectralSquares (![1,0] : Fin 2 → ℝ) := by
  norm_num [spectralSquares,cutPair,Fin.sum_univ_two]

theorem quadratic_convexity_cannot_be_dropped :
    (-(1/2:ℝ)^2+(1/2:ℝ)) > max (0:ℝ) (-1+1) := by norm_num

theorem ordered_weight_regression :
    orderedSimplexWeight (![3/5,3/10,1/10] : Fin 3 → ℝ) 1=2/5 := by
  norm_num [orderedSimplexWeight,spectrumDifference,spectrumZeroExtend]

end APPTReview
