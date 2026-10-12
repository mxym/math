import GaussianBalancedBVProfile
import Mathlib.Analysis.SpecificLimits.Basic

/-! A genuine minimizing sequence of actual measurable equal-mass Gaussian
clusters, with uniformly bounded finite BV perimeter. This uses the proved
regular competitor and the infimum property. Existence of an L1-convergent
subsequence and of a minimizer are separate remaining geometric steps. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge

theorem exists_balanced_BV_minimizing_sequence (d : ℕ) :
    ∃ C : ℕ → BalancedGaussianCluster (d+1) (d+2),
      (∀ n,(C n).perimeter ≠ (∞ : ℝ≥0∞)) ∧
      (∀ n,(C n).perimeter ≤
        ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2))+1) ∧
      Tendsto (fun n => (C n).perimeter) atTop (𝓝 (balancedGaussianBVProfile d)) := by
  classical
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1/((n:ℝ)+1))
  have hε (n : ℕ) : ε n ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    have hh : (1 : ℝ)/((n:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hh
  have hex (n : ℕ) : ∃ C : BalancedGaussianCluster (d+1) (d+2),
      C.perimeter < balancedGaussianBVProfile d+ε n := by
    have hh := ENNReal.lt_add_right (balancedGaussianBVProfile_ne_top d) (hε n)
    exact iInf_lt_iff.mp hh
  choose C hC using hex
  have hlo (n : ℕ) : balancedGaussianBVProfile d ≤ (C n).perimeter :=
    iInf_le (fun D : BalancedGaussianCluster (d+1) (d+2) => D.perimeter) (C n)
  have hfin (n : ℕ) : (C n).perimeter ≠ (∞ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top _ (hC n).le
    exact ENNReal.add_ne_top.mpr ⟨balancedGaussianBVProfile_ne_top d,ENNReal.ofReal_ne_top⟩
  have hbound (n : ℕ) : (C n).perimeter ≤
      ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2))+1 :=
    (hC n).le.trans (add_le_add (balancedGaussianBVProfile_le_model d) (hε1 n))
  have heps : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htop : Tendsto (fun n => balancedGaussianBVProfile d+ε n) atTop
      (𝓝 (balancedGaussianBVProfile d)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := balancedGaussianBVProfile d)).add heps
  refine ⟨C,hfin,hbound,?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop hlo (fun n => (hC n).le)

end GaussianMeasureBridge
