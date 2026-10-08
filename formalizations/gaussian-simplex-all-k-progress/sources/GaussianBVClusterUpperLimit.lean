import GaussianBVClusterLimit
import GaussianBalancedBVProfile

/-! Total cluster BV perimeter is lower semicontinuous under actual
indicator-L1 convergence, including a convergent sequence of upper bounds.
An actual balanced L1 limit of a minimizing sequence is therefore a
minimizer. The existence of that L1 limit is not assumed implicitly. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

theorem gaussian_total_BV_upper_limit_under_indicatorL1
    (S : Fin k → Set (Space d)) (T : ℕ → Fin k → Set (Space d))
    (G : ℕ → ℝ≥0∞) (P : ℝ≥0∞)
    (hS : ∀ i,MeasurableSet (S i)) (hT : ∀ n i,MeasurableSet (T n i))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance (T n i) (S i)) atTop (𝓝 0))
    (hupper : ∀ n,(∑ i,gaussianBVPerimeter (T n i))/2 ≤ G n)
    (hG : Tendsto G atTop (𝓝 P)) :
    (∑ i,gaussianBVPerimeter (S i))/2 ≤ P := by
  rw [sum_gaussianBVPerimeter_eq_iSup_tests,ENNReal.iSup_div]
  apply iSup_le
  intro X
  have h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht := tendsto_finsetSum Finset.univ (fun i _ => ENNReal.tendsto_ofReal
    (gaussian_test_integral_tendsto_of_indicatorL1 (S i) (fun n => T n i)
      (hS i) (fun n => hT n i) (hdist i) (X i)))
  have hhalf := ENNReal.Tendsto.div_const ht (Or.inr h2z)
  apply le_of_tendsto_of_tendsto hhalf hG
  exact Eventually.of_forall fun n =>
    (ENNReal.div_le_div_right
      (Finset.sum_le_sum (fun i _ => gaussianBVPerimeter_ge_test (T n i) (X i))) 2).trans (hupper n)

theorem balanced_BV_minimizer_of_indicatorL1_limit
    (d : ℕ) (C : ℕ → BalancedGaussianCluster (d+1) (d+2))
    (D : BalancedGaussianCluster (d+1) (d+2))
    (hper : Tendsto (fun n => (C n).perimeter) atTop (𝓝 (balancedGaussianBVProfile d)))
    (hdist : ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance ((C n).cell i) (D.cell i)) atTop (𝓝 0)) :
    D.perimeter=balancedGaussianBVProfile d := by
  apply le_antisymm
  · exact gaussian_total_BV_upper_limit_under_indicatorL1 D.cell (fun n => (C n).cell)
      (fun n => (C n).perimeter) (balancedGaussianBVProfile d) D.measurable
      (fun n => (C n).measurable) hdist (fun _ => le_rfl) hper
  · exact iInf_le (fun E : BalancedGaussianCluster (d+1) (d+2) => E.perimeter) D

end GaussianMeasureBridge
