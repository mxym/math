import GaussianScaledCutoffGradient
import GaussianHalfspaceFlux

/-! Genuine compact Gaussian test fields built from the expanding cutoffs
and a coordinate vector, with their exact divergence formula. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def coordinateCutoffTest (N : ℕ) (i : Fin d) : GaussianTestField d :=
  { toFun := fun x => scaledGaussianCutoff d N x • EuclideanSpace.basisFun (Fin d) ℝ i
    smooth := (scaledGaussianCutoff_contDiff N).smul contDiff_const
    compact := (scaledGaussianCutoff_compact N).smul_right
      (f' := fun _ => EuclideanSpace.basisFun (Fin d) ℝ i)
    norm_le := fun x => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (scaledGaussianCutoff_bounds N x).1,
        (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,mul_one]
      exact (scaledGaussianCutoff_bounds N x).2 }

lemma coordinateCutoffTest_divergence (N : ℕ) (i : Fin d) (x : Space d) :
    gaussianDivergence (coordinateCutoffTest N i) x =
      fderiv ℝ (scaledGaussianCutoff d N) x (EuclideanSpace.basisFun (Fin d) ℝ i)-
        x i*scaledGaussianCutoff d N x := by
  have hd : Differentiable ℝ (scaledGaussianCutoff d N) :=
    (scaledGaussianCutoff_contDiff N).differentiable (by simp)
  have hf : fderiv ℝ (coordinateCutoffTest N i) x =
      (fderiv ℝ (scaledGaussianCutoff d N) x).smulRight (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    convert ((hd x).hasFDerivAt.smul_const (EuclideanSpace.basisFun (Fin d) ℝ i)).fderiv using 1
    rfl
  have hs : (∑ j : Fin d,fderiv ℝ (scaledGaussianCutoff d N) x
      (EuclideanSpace.basisFun (Fin d) ℝ j)*EuclideanSpace.basisFun (Fin d) ℝ i j) =
      fderiv ℝ (scaledGaussianCutoff d N) x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    have he := congrArg (fderiv ℝ (scaledGaussianCutoff d N) x)
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (EuclideanSpace.basisFun (Fin d) ℝ i))
    simpa only [map_sum,map_smul,EuclideanSpace.basisFun_inner,smul_eq_mul,mul_comm] using he
  unfold gaussianDivergence
  rw [hf]
  change (∑ j : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ j,
      fderiv ℝ (scaledGaussianCutoff d N) x (EuclideanSpace.basisFun (Fin d) ℝ j) •
        EuclideanSpace.basisFun (Fin d) ℝ i⟫)-
    ⟪x,scaledGaussianCutoff d N x • EuclideanSpace.basisFun (Fin d) ℝ i⟫ = _
  simp only [real_inner_smul_right,EuclideanSpace.basisFun_inner,EuclideanSpace.inner_basisFun_real,
    PiLp.smul_apply,smul_eq_mul]
  rw [hs,mul_comm (scaledGaussianCutoff d N x) (x i)]

lemma coordinate_gaussian_integrable (i : Fin d) :
    Integrable (fun x : Space d => x i) (gaussian d) := by
  simpa only [EuclideanSpace.basisFun_inner] using
    integrable_gaussian_inner (EuclideanSpace.basisFun (Fin d) ℝ i)

end GaussianMeasureBridge
