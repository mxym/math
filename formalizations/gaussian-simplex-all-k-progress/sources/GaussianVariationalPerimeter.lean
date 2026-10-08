import GaussianRealBVPerimeter
import GaussianPartition
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! The conventional Gaussian variational perimeter in arbitrary Euclidean
dimension, using actual smooth compact vector fields and Gaussian divergence.
This supplies definitions and test-field bounds for the pending BV bridge. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def gaussianDivergence (X : Space d → Space d) (x : Space d) : ℝ :=
  (∑ i : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ i,
    fderiv ℝ X x (EuclideanSpace.basisFun (Fin d) ℝ i)⟫)-⟪x,X x⟫

structure GaussianTestField (d : ℕ) where
  toFun : Space d → Space d
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  norm_le : ∀ x,‖toFun x‖ ≤ 1

instance : CoeFun (GaussianTestField d) (fun _ => Space d → Space d) := ⟨GaussianTestField.toFun⟩

noncomputable def gaussianBVPerimeter (S : Set (Space d)) : ℝ≥0∞ :=
  ⨆ X : GaussianTestField d,ENNReal.ofReal (∫ x in S,gaussianDivergence X x ∂gaussian d)

lemma gaussianDivergence_continuous (X : GaussianTestField d) : Continuous (gaussianDivergence X) := by
  have hc := X.smooth.continuous
  have hd := X.smooth.continuous_fderiv (by simp)
  unfold gaussianDivergence
  fun_prop

lemma gaussianDivergence_hasCompactSupport (X : GaussianTestField d) :
    HasCompactSupport (gaussianDivergence X) := by
  apply X.compact.mono'
  intro x hx
  by_contra he
  have hz : X x = 0 := Function.notMem_support.mp (fun h => he (subset_tsupport _ h))
  apply hx
  simp only [gaussianDivergence,fderiv_of_notMem_tsupport ℝ he,hz,
    ContinuousLinearMap.zero_apply,inner_zero_right,Finset.sum_const_zero,sub_zero]

theorem gaussianDivergence_integrable (X : GaussianTestField d) :
    Integrable (gaussianDivergence X) (gaussian d) :=
  (gaussianDivergence_continuous X).integrable_of_hasCompactSupport
    (gaussianDivergence_hasCompactSupport X)

theorem gaussianBVPerimeter_ge_test (S : Set (Space d)) (X : GaussianTestField d) :
    ENNReal.ofReal (∫ x in S,gaussianDivergence X x ∂gaussian d) ≤ gaussianBVPerimeter S :=
  le_iSup (fun Y : GaussianTestField d =>
    ENNReal.ofReal (∫ x in S,gaussianDivergence Y x ∂gaussian d)) X

end GaussianMeasureBridge
