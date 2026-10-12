import GaussianAllCoordinateStein
import GaussianVariationalPerimeter

/-! The actual Gaussian divergence theorem on the whole Euclidean space for
smooth compactly supported vector fields, proved from coordinate integration
by parts. No boundary or minimizer regularity assumption is used. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma coordinate_of_field_contDiff (X : Space d → Space d) (hX : ContDiff ℝ 1 X)
    (i : Fin d) : ContDiff ℝ 1 (fun x => X x i) := by
  exact (EuclideanSpace.proj i : Space d →L[ℝ] ℝ).contDiff.comp hX

lemma coordinate_of_field_compact (X : Space d → Space d) (hX : HasCompactSupport X)
    (i : Fin d) : HasCompactSupport (fun x => X x i) :=
  hX.comp_left (g := fun z : Space d => z i) rfl

lemma coordinate_of_field_fderiv (X : Space d → Space d) (hX : Differentiable ℝ X)
    (i : Fin d) (x u : Space d) :
    fderiv ℝ (fun z => X z i) x u = (fderiv ℝ X x u) i := by
  have he := ((EuclideanSpace.proj i).hasFDerivAt.comp x (hX x).hasFDerivAt).fderiv
  exact congrArg (fun A : Space d →L[ℝ] ℝ => A u) he

lemma gaussianDivergence_coordinate_sum (X : Space (d+1) → Space (d+1))
    (hX : Differentiable ℝ X) (x : Space (d+1)) :
    gaussianDivergence X x = ∑ i : Fin (d+1),coordinateStein i (fun z => X z i) x := by
  simp only [gaussianDivergence,EuclideanSpace.basisFun_inner,coordinateStein,
    coordinate_of_field_fderiv X hX,Finset.sum_sub_distrib]
  congr 1
  simp [PiLp.inner_apply,mul_comm]

theorem gaussianDivergence_integral_zero (X : GaussianTestField d) :
    (∫ x,gaussianDivergence X x ∂gaussian d) = 0 := by
  cases d with
  | zero => simp [gaussianDivergence,PiLp.inner_apply]
  | succ d =>
    have hc : ContDiff ℝ 1 X := X.smooth.of_le (by simp)
    have hi (i : Fin (d+1)) : Integrable (coordinateStein i (fun z => X z i))
        (gaussian (d+1)) :=
      (coordinateStein_continuous i _ (coordinate_of_field_contDiff X hc i)).integrable_of_hasCompactSupport
        (coordinateStein_compact i _ (coordinate_of_field_compact X X.compact i))
    simp_rw [gaussianDivergence_coordinate_sum X (hc.differentiable one_ne_zero)]
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [gaussian_coordinate_stein _ _ (coordinate_of_field_contDiff X hc _)
      (coordinate_of_field_compact X X.compact _),Finset.sum_const_zero]

end GaussianMeasureBridge
