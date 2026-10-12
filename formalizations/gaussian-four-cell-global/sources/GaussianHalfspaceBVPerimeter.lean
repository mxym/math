import GaussianHalfspaceTestFlux
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact conventional Gaussian BV perimeter of a coordinate halfspace in
arbitrary dimension. The sharp lower bound is obtained with an explicit
sequence of genuine smooth compact vector fields and dominated convergence. -/
open MeasureTheory ProbabilityTheory Module Set Metric Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma joinCoordinate_slice_continuous (a : ℝ) : Continuous (joinCoordinate (d := d) a) := by
  unfold joinCoordinate
  fun_prop

lemma testField_coordinate_abs_le_one (X : GaussianTestField d) (x : Space d) (i : Fin d) :
    |X x i| ≤ 1 := by
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (X x) i).trans (X.norm_le x)

noncomputable def gaussianCutoff (d N : ℕ) : ContDiffBump (0 : Space d) :=
  ⟨(N : ℝ)+1,(N : ℝ)+2,by positivity,by linarith⟩

lemma gaussianCutoff_tendsto (x : Space d) :
    Tendsto (fun N : ℕ => gaussianCutoff d N x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  have he : (fun n : ℕ => gaussianCutoff d n x) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply (gaussianCutoff d n).one_of_mem_closedBall
    change dist x 0 ≤ (n : ℝ)+1
    rw [dist_zero_right]
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact tendsto_const_nhds.congr' he.symm

noncomputable def negativeCoordinateCutoff (d N : ℕ) : GaussianTestField (d+1) :=
  { toFun := fun x => -(gaussianCutoff (d+1) N x) • EuclideanSpace.basisFun (Fin (d+1)) ℝ 0
    smooth := (gaussianCutoff (d+1) N).contDiff.neg.smul contDiff_const
    compact := (gaussianCutoff (d+1) N).hasCompactSupport.neg.smul_right
    norm_le := fun x => by
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (gaussianCutoff (d+1) N).nonneg,
        (EuclideanSpace.basisFun (Fin (d+1)) ℝ).norm_eq_one,mul_one]
      exact (gaussianCutoff (d+1) N).le_one }

lemma negativeCoordinateCutoff_normal (N : ℕ) (x : Space (d+1)) :
    negativeCoordinateCutoff d N x 0 = -gaussianCutoff (d+1) N x := by
  simp [negativeCoordinateCutoff,EuclideanSpace.basisFun_apply]

lemma gaussianCutoff_boundary_integral_tendsto (a : ℝ) :
    Tendsto (fun N : ℕ => ∫ y,gaussianCutoff (d+1) N (joinCoordinate a y) ∂gaussian d)
      atTop (𝓝 1) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := gaussian d)
    (F := fun N y => gaussianCutoff (d+1) N (joinCoordinate a y))
    (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun N => ((gaussianCutoff (d+1) N).continuous.comp (joinCoordinate_slice_continuous a)).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (gaussianCutoff (d+1) N).nonneg]
      exact (gaussianCutoff (d+1) N).le_one)
    (ae_of_all _ fun y => gaussianCutoff_tendsto (joinCoordinate a y))
  simpa using hlim

theorem gaussianBVPerimeter_coordinate_halfspace (a : ℝ) :
    gaussianBVPerimeter {x : Space (d+1) | a < x 0} = ENNReal.ofReal (standardDensity a) := by
  apply le_antisymm
  · apply iSup_le
    intro X
    apply ENNReal.ofReal_le_ofReal
    rw [gaussian_halfspace_test_divergence]
    have hi : Integrable (fun y : Space d => -X (joinCoordinate a y) 0) (gaussian d) :=
      (integrable_const (1 : ℝ)).mono'
        (by
          have hc : Continuous (fun y : Space d => -X (joinCoordinate a y) 0) := by
            have hX := X.smooth.continuous.comp (joinCoordinate_slice_continuous (d := d) a)
            fun_prop
          exact hc.aestronglyMeasurable)
        (ae_of_all _ fun y => by
          simpa only [norm_neg,Real.norm_eq_abs] using testField_coordinate_abs_le_one X _ 0)
    have hbound : (∫ y : Space d,-X (joinCoordinate a y) 0 ∂gaussian d) ≤ 1 := by
      have hb := integral_mono_ae hi (integrable_const (1 : ℝ))
        (ae_of_all _ fun y => (neg_le_abs _).trans (testField_coordinate_abs_le_one X _ 0))
      simpa using hb
    rw [integral_neg] at hbound
    have hp := standardDensity_pos a
    nlinarith
  · have hreal : Tendsto (fun N : ℕ => standardDensity a *
        (∫ y,gaussianCutoff (d+1) N (joinCoordinate a y) ∂gaussian d)) atTop
        (𝓝 (standardDensity a)) := by
      simpa using tendsto_const_nhds.mul (gaussianCutoff_boundary_integral_tendsto (d := d) a)
    have hen := (ENNReal.continuous_ofReal.tendsto (standardDensity a)).comp hreal
    apply le_of_tendsto hen
    exact Eventually.of_forall fun N => by
      have hb := gaussianBVPerimeter_ge_test {x : Space (d+1) | a < x 0} (negativeCoordinateCutoff d N)
      rw [gaussian_halfspace_test_divergence] at hb
      simp only [negativeCoordinateCutoff_normal,integral_neg,mul_neg] at hb
      simpa only [Function.comp_def,neg_mul,neg_neg] using hb

end GaussianMeasureBridge
