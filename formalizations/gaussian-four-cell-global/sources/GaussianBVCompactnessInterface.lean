import GaussianBVMinimizerFromLimit

/-! Precise remaining Gaussian BV compactness obligation. The reduction
from this genuine indicator-L1 subsequence statement to existence of an
actual equal-mass minimizing cluster is proved. Compactness, geometric
regularity and the sharp perimeter lower bound are not asserted. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge

def GaussianClusterBVCompactness (d k : ℕ) : Prop :=
  ∀ C : ℕ → BalancedGaussianCluster d k,∀ P : ℝ,
    (∀ n,(C n).perimeter ≤ ENNReal.ofReal P) →
    ∃ τ : ℕ → ℕ,StrictMono τ ∧ ∃ S : Fin k → Set (Space d),
      (∀ i,MeasurableSet (S i)) ∧
      ∀ i,Tendsto (fun n => gaussianIndicatorL1Distance ((C (τ n)).cell i) (S i)) atTop (𝓝 0)

theorem exists_balanced_BV_minimizer_of_compactness
    (d : ℕ) (hcompact : GaussianClusterBVCompactness (d+1) (d+2)) :
    ∃ D : BalancedGaussianCluster (d+1) (d+2),D.perimeter=balancedGaussianBVProfile d := by
  obtain ⟨C,_,hbound,hper⟩ := exists_balanced_BV_minimizing_sequence d
  let R : ℝ := simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2)
  have hR : 0 ≤ R := mul_nonneg (simplexConstant_nonneg (k := d+2)) (Real.sqrt_nonneg _)
  have hb (n : ℕ) : (C n).perimeter ≤ ENNReal.ofReal (R+1) := by
    rw [ENNReal.ofReal_add hR (by norm_num),ENNReal.ofReal_one]
    exact hbound n
  obtain ⟨τ,hτ,S,hS,hdist⟩ := hcompact C (R+1) hb
  have hp : Tendsto (fun n => (C (τ n)).perimeter) atTop (𝓝 (balancedGaussianBVProfile d)) :=
    hper.comp hτ.tendsto_atTop
  obtain ⟨D,hD,_⟩ := exists_balanced_BV_minimizer_of_cellwise_indicatorL1_limit d
    (fun n => C (τ n)) hp S hS hdist
  exact ⟨D,hD⟩

end GaussianMeasureBridge
