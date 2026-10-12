import BapatGaussianRatioIntegral
import BapatGaussianSphereAverage

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set

namespace BapatRealExistence
noncomputable section

abbrev RealPair4 := WithLp 2 (RealSpace4 × RealSpace4)

def ratioBlockShuffle : RealPair4 ≃ₗᵢ[ℝ] RealPair4 where
  toFun p := WithLp.toLp 2
    (WithLp.toLp 2 ![p.ofLp.1 0,p.ofLp.1 1,p.ofLp.2 0,p.ofLp.2 1],
     WithLp.toLp 2 ![p.ofLp.1 2,p.ofLp.1 3,p.ofLp.2 2,p.ofLp.2 3])
  invFun p := WithLp.toLp 2
    (WithLp.toLp 2 ![p.ofLp.1 0,p.ofLp.1 1,p.ofLp.2 0,p.ofLp.2 1],
     WithLp.toLp 2 ![p.ofLp.1 2,p.ofLp.1 3,p.ofLp.2 2,p.ofLp.2 3])
  left_inv p := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv p := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_add' p q := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_smul' r p := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  norm_map' p := by
    change ‖WithLp.toLp 2
      (WithLp.toLp 2 ![p.ofLp.1 0,p.ofLp.1 1,p.ofLp.2 0,p.ofLp.2 1],
       WithLp.toLp 2 ![p.ofLp.1 2,p.ofLp.1 3,p.ofLp.2 2,p.ofLp.2 3])‖ = ‖p‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [WithLp.prod_norm_sq_eq_of_L2,WithLp.fst,WithLp.snd]
    simp only [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_succ]
    <;> ring

def realFourComplexMeasurable : RealSpace4 ≃ᵐ (ℂ × ℂ) :=
  realFourComplexPair.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (ℂ × ℂ)).symm

theorem realFourComplexMeasurable_preserving : MeasurePreserving realFourComplexMeasurable :=
  (WithLp.volume_preserving_ofLp ℂ ℂ).comp realFourComplexPair.measurePreserving

def realPairShuffle : (RealSpace4 × RealSpace4) ≃ᵐ (RealSpace4 × RealSpace4) :=
  ((MeasurableEquiv.toLp 2 (RealSpace4 × RealSpace4)).trans
    ratioBlockShuffle.toHomeomorph.toMeasurableEquiv).trans
      (MeasurableEquiv.toLp 2 (RealSpace4 × RealSpace4)).symm

theorem realPairShuffle_preserving : MeasurePreserving realPairShuffle :=
  (WithLp.volume_preserving_ofLp RealSpace4 RealSpace4).comp
    (ratioBlockShuffle.measurePreserving.comp (WithLp.volume_preserving_toLp RealSpace4 RealSpace4))

def ratioRegroup : (RealSpace4 × RealSpace4) ≃ᵐ ((ℂ × ℂ) × RealSpace4) :=
  realPairShuffle.trans (realFourComplexMeasurable.prodCongr (MeasurableEquiv.refl RealSpace4))

theorem ratioRegroup_preserving : MeasurePreserving ratioRegroup :=
  (realFourComplexMeasurable_preserving.prod (MeasurePreserving.id volume)).comp realPairShuffle_preserving

theorem balancedRealRatio_eq_complex (v : RealSpace4) :
    balancedRealRatio v = (complexPair (v 2) (v 3)/complexPair (v 0) (v 1)).re := by
  rw [← complexRowRatio_balanced,← realRowRatio_balanced]
  rfl

def pairRatioGaussian (x y : RealSpace4) : ℝ :=
  |balancedRealRatio x-balancedRealRatio y| * Real.exp (-‖y‖^2)*Real.exp (-‖x‖^2)

theorem ratioRegroup_kernel (p : RealSpace4 × RealSpace4) :
    gaussianRatioKernel (ratioRegroup p).1.1 (ratioRegroup p).1.2 (ratioRegroup p).2 =
      pairRatioGaussian p.1 p.2 := by
  let d : RealSpace4 := WithLp.toLp 2 ![p.1 0,p.1 1,p.2 0,p.2 1]
  let n : RealSpace4 := WithLp.toLp 2 ![p.1 2,p.1 3,p.2 2,p.2 3]
  have hn : ‖n‖^2+‖complexPair (p.1 0) (p.1 1)‖^2+‖complexPair (p.2 0) (p.2 1)‖^2 =
      ‖p.1‖^2+‖p.2‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,complexPair_norm_sq]
    simp [n,Fin.sum_univ_succ]
    <;> ring
  change gaussianRatioKernel (complexPair (p.1 0) (p.1 1)) (complexPair (p.2 0) (p.2 1)) n = _
  unfold gaussianRatioKernel pairRatioGaussian
  rw [ratioDifferenceCoefficient_inner]
  change |(complexPair (p.1 2) (p.1 3)/complexPair (p.1 0) (p.1 1)).re-
    (complexPair (p.2 2) (p.2 3)/complexPair (p.2 0) (p.2 1)).re| *
      Real.exp (-‖n‖^2)*Real.exp (-(‖complexPair (p.1 0) (p.1 1)‖^2+‖complexPair (p.2 0) (p.2 1)‖^2)) = _
  rw [← balancedRealRatio_eq_complex,← balancedRealRatio_eq_complex]
  simp only [mul_assoc,← Real.exp_add]
  congr 2
  linarith

theorem pairRatioGaussian_integrable :
    Integrable (fun p : RealSpace4 × RealSpace4 => pairRatioGaussian p.1 p.2) := by
  have h := (ratioRegroup_preserving.integrable_comp_emb ratioRegroup.measurableEmbedding).mpr
    gaussianRatioKernel_integrable
  simpa only [Function.comp_def,ratioRegroup_kernel] using h

theorem pairRatioGaussian_integral :
    (∫ x : RealSpace4, ∫ y : RealSpace4, pairRatioGaussian x y) = Real.pi^5/2 := by
  have hc := ratioRegroup_preserving.integral_comp ratioRegroup.measurableEmbedding
    (fun p : (ℂ × ℂ) × RealSpace4 => gaussianRatioKernel p.1.1 p.1.2 p.2)
  simp only [ratioRegroup_kernel] at hc
  rw [Measure.volume_eq_prod,integral_prod _ pairRatioGaussian_integrable] at hc
  exact hc.trans gaussianRatioKernel_integral

/-- Exact Gini mean difference of real parts of the balanced Gaussian/sphere ratios. -/
theorem sphere_balancedRealRatio_gini :
    (∫ x : RealUnitSphere4, ∫ y : RealUnitSphere4, |balancedRealRatio x-balancedRealRatio y|
      ∂normalizedSphere (volume : Measure RealSpace4)
      ∂normalizedSphere (volume : Measure RealSpace4)) = Real.pi/2 := by
  have h := homogeneous_pair_gaussian_sphere_average
    (fun x y => |balancedRealRatio x-balancedRealRatio y|)
    (by intro r hr x y; rw [balancedRealRatio_smul x r hr.ne'])
    (by intro r hr x y; rw [balancedRealRatio_smul y r hr.ne'])
  change (∫ x : RealSpace4, ∫ y : RealSpace4, pairRatioGaussian x y) = _ at h
  rw [pairRatioGaussian_integral] at h
  have hp : Real.pi^4 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  apply (mul_left_cancel₀ hp)
  rw [← h]
  ring

end
end BapatRealExistence
