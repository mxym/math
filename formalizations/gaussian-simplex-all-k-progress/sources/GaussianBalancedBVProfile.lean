import GaussianSimplicialBVUpperBridge
import GaussianRegularPerimeter
import GaussianBVClusterLimit

/-! The genuine equal-mass Gaussian BV minimization problem is nonempty
and has a finite competitor, constructed from actual regular scores. The
profile upper bound is unconditional. The sharp reverse bound and existence
of a minimizing cluster are not asserted. -/
open MeasureTheory ProbabilityTheory Module Set Filter Matrix
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem actual_regular_cluster_BV_upper
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i=0) (hg : scoreGram v=regularCovariance (d+2)) :
    (canonicalWinningCluster v hv.injective).perimeter ≤
      ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2)) := by
  let S : ℝ := (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2
  have hp (i : Fin (d+2)) := canonical_simplicial_inner_perimeter_nonneg v hv i
  have hS0 : 0 ≤ S := div_nonneg (Finset.sum_nonneg (fun i _ => hp i)) (by norm_num)
  have hSq : S^2=(d+1:ℕ)*simplexConstant (d+2)^2/2 :=
    regular_intrinsic_cluster_perimeter_squared v hv hz hg
  have hroot := Real.sq_sqrt (show 0 ≤ ((d+1:ℕ):ℝ)/2 by positivity)
  have hc := simplexConstant_nonneg (k := d+2)
  have hroot0 := Real.sqrt_nonneg (((d+1:ℕ):ℝ)/2)
  have he : S=simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2) := by
    have hsq : S^2=(simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2))^2 := by
      rw [mul_pow,hroot]
      nlinarith [hSq]
    exact (sq_eq_sq₀ hS0 (mul_nonneg hc hroot0)).mp hsq
  rw [← he]
  change (∑ i,gaussianBVPerimeter (winningCell v (canonicalPrices v) i))/2 ≤
    ENNReal.ofReal ((∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i)]
  simpa using ENNReal.div_le_div_right
    (Finset.sum_le_sum (fun i _ => actual_simplicial_cell_BV_upper v (canonicalPrices v) hv i)) 2

theorem exists_balanced_cluster_with_model_BV_upper (d : ℕ) :
    ∃ C : BalancedGaussianCluster (d+1) (d+2),
      C.perimeter ≤ ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2)) := by
  let v : Fin (d+2) → Space (d+1) := minimalCovarianceRows (regularCovariance (d+2))
  have hR := regularCovariance_normalized (k := d+2) (by omega)
  have hv : AffineIndependent ℝ v := minimalCovarianceRows_affineIndependent _ regular_principal_posDef
  have hz : ∑ i,v i=0 := minimalCovarianceRows_sum _
  have hg : scoreGram v=regularCovariance (d+2) := scoreGram_minimalCovarianceRows _ hR.1 hR.2.1
  exact ⟨canonicalWinningCluster v hv.injective,actual_regular_cluster_BV_upper v hv hz hg⟩

noncomputable def balancedGaussianBVProfile (d : ℕ) : ℝ≥0∞ :=
  ⨅ C : BalancedGaussianCluster (d+1) (d+2),C.perimeter

theorem balancedGaussianBVProfile_le_model (d : ℕ) :
    balancedGaussianBVProfile d ≤
      ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2)) := by
  obtain ⟨C,hC⟩ := exists_balanced_cluster_with_model_BV_upper d
  exact (iInf_le (fun C : BalancedGaussianCluster (d+1) (d+2) => C.perimeter) C).trans hC

theorem balancedGaussianBVProfile_ne_top (d : ℕ) : balancedGaussianBVProfile d ≠ (∞ : ℝ≥0∞) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (balancedGaussianBVProfile_le_model d)

end GaussianMeasureBridge
