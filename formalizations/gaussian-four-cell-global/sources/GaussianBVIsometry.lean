import GaussianHalfspaceBVPerimeter

/-! Orthogonal invariance of the conventional Gaussian BV perimeter.
The divergence transformation is proved by orthonormal expansion and the
actual Gaussian measure-preserving law. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma diagonal_inner_basis_independent (A : Space d →L[ℝ] Space d)
    (b c : OrthonormalBasis (Fin d) ℝ (Space d)) :
    (∑ i,⟪b i,A (b i)⟫) = ∑ j,⟪c j,A (c j)⟫ := by
  calc
    _ = ∑ i,⟪b i,A (∑ j,⟪c j,b i⟫ • c j)⟫ := by simp only [c.sum_repr']
    _ = ∑ i,∑ j,⟪c j,b i⟫*⟪b i,A (c j)⟫ := by
      simp only [map_sum,map_smul,inner_sum,real_inner_smul_right]
    _ = ∑ j,∑ i,⟪c j,b i⟫*⟪b i,A (c j)⟫ := Finset.sum_comm
    _ = _ := by simp only [b.sum_inner_mul_inner]

noncomputable def pullGaussianTestField (T : Space d ≃ₗᵢ[ℝ] Space d)
    (X : GaussianTestField d) : GaussianTestField d :=
  { toFun := fun x => T.symm (X (T x))
    smooth := T.symm.toContinuousLinearEquiv.contDiff.comp
      (X.smooth.comp T.toContinuousLinearEquiv.contDiff)
    compact := (X.compact.comp_homeomorph T.toHomeomorph).comp_left T.symm.map_zero
    norm_le := fun x => by rw [T.symm.norm_map]; exact X.norm_le (T x) }

lemma gaussianDivergence_pull (T : Space d ≃ₗᵢ[ℝ] Space d) (X : GaussianTestField d)
    (x : Space d) : gaussianDivergence (pullGaussianTestField T X) x = gaussianDivergence X (T x) := by
  have hdiff : Differentiable ℝ X := X.smooth.differentiable (by simp)
  have hf : fderiv ℝ (pullGaussianTestField T X) x =
      T.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        fderiv ℝ X (T x) ∘L T.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact (T.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      ((hdiff (T x)).hasFDerivAt.comp x
        T.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)).fderiv
  have hi (u w : Space d) : ⟪u,T.symm w⟫ = ⟪T u,w⟫ := by
    rw [← T.inner_map_map,T.apply_symm_apply]
  have ht := diagonal_inner_basis_independent (fderiv ℝ X (T x))
    ((EuclideanSpace.basisFun (Fin d) ℝ).map T) (EuclideanSpace.basisFun (Fin d) ℝ)
  unfold gaussianDivergence
  rw [hf]
  change (∑ i : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ i,
    T.symm (fderiv ℝ X (T x) (T (EuclideanSpace.basisFun (Fin d) ℝ i)))⟫)-
      ⟪x,T.symm (X (T x))⟫ = _
  simp_rw [hi]
  simpa only [OrthonormalBasis.map_apply] using congrArg (fun z : ℝ => z-⟪T x,X (T x)⟫) ht

lemma gaussian_test_integral_isometry (T : Space d ≃ₗᵢ[ℝ] Space d)
    (S : Set (Space d)) (hS : MeasurableSet S) (X : GaussianTestField d) :
    (∫ x in T ⁻¹' S,gaussianDivergence (pullGaussianTestField T X) x ∂gaussian d) =
      ∫ x in S,gaussianDivergence X x ∂gaussian d := by
  have hm : MeasurePreserving T (gaussian d) (gaussian d) :=
    ⟨T.continuous.measurable,stdGaussian_map T⟩
  rw [← integral_indicator (hS.preimage T.continuous.measurable),← integral_indicator hS]
  have he : (T ⁻¹' S).indicator (gaussianDivergence (pullGaussianTestField T X)) =
      (S.indicator (gaussianDivergence X)) ∘ T := by
    funext x
    by_cases hx : T x ∈ S <;> simp [hx,gaussianDivergence_pull]
  rw [he]
  have hi := integral_map (μ := gaussian d) hm.measurable.aemeasurable
    (((gaussianDivergence_continuous X).measurable.indicator hS).aestronglyMeasurable
      (μ := Measure.map T (gaussian d)))
  rw [hm.map_eq] at hi
  exact hi.symm

theorem gaussianBVPerimeter_isometry (T : Space d ≃ₗᵢ[ℝ] Space d)
    (S : Set (Space d)) (hS : MeasurableSet S) :
    gaussianBVPerimeter (T ⁻¹' S) = gaussianBVPerimeter S := by
  have hle (T : Space d ≃ₗᵢ[ℝ] Space d) (S : Set (Space d)) (hS : MeasurableSet S) :
      gaussianBVPerimeter S ≤ gaussianBVPerimeter (T ⁻¹' S) := by
    apply iSup_le
    intro X
    rw [← gaussian_test_integral_isometry T S hS X]
    exact gaussianBVPerimeter_ge_test _ (pullGaussianTestField T X)
  apply le_antisymm
  · have hh := hle T.symm (T ⁻¹' S) (hS.preimage T.continuous.measurable)
    have he : T.symm ⁻¹' (T ⁻¹' S) = S := by ext x; simp
    simpa only [he] using hh
  · exact hle T S hS

end GaussianMeasureBridge
