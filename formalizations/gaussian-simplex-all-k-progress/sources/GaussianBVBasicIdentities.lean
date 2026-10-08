import GaussianDivergenceStein

/-! Basic identities for the genuine variational Gaussian perimeter. They
follow from actual whole-space Stein integration, including complement
invariance and invariance under Gaussian-null modifications. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def negGaussianTestField (X : GaussianTestField d) : GaussianTestField d :=
  { toFun := fun x => -X x
    smooth := X.smooth.neg
    compact := X.compact.neg
    norm_le := fun x => by rw [norm_neg]; exact X.norm_le x }

lemma gaussianDivergence_neg (X : GaussianTestField d) (x : Space d) :
    gaussianDivergence (negGaussianTestField X) x = -gaussianDivergence X x := by
  change (∑ i : Fin d,⟪EuclideanSpace.basisFun (Fin d) ℝ i,
    fderiv ℝ (fun y => -X y) x (EuclideanSpace.basisFun (Fin d) ℝ i)⟫)-⟪x,-X x⟫ = _
  rw [fderiv_fun_neg]
  simp only [neg_apply,inner_neg_right,Finset.sum_neg_distrib,gaussianDivergence]
  ring

lemma gaussianBVPerimeter_compl_le (S : Set (Space d)) (hS : MeasurableSet S) :
    gaussianBVPerimeter Sᶜ ≤ gaussianBVPerimeter S := by
  apply iSup_le
  intro X
  have hc := setIntegral_compl hS (gaussianDivergence_integrable X)
  rw [gaussianDivergence_integral_zero,zero_sub] at hc
  have hn : (∫ x in S,gaussianDivergence (negGaussianTestField X) x ∂gaussian d) =
      -(∫ x in S,gaussianDivergence X x ∂gaussian d) := by
    simp only [gaussianDivergence_neg,integral_neg]
  rw [hc,← hn]
  exact gaussianBVPerimeter_ge_test S (negGaussianTestField X)

theorem gaussianBVPerimeter_compl (S : Set (Space d)) (hS : MeasurableSet S) :
    gaussianBVPerimeter Sᶜ = gaussianBVPerimeter S := by
  apply le_antisymm (gaussianBVPerimeter_compl_le S hS)
  simpa only [compl_compl] using gaussianBVPerimeter_compl_le Sᶜ hS.compl

theorem gaussianBVPerimeter_congr_ae (S T : Set (Space d))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : ∀ᵐ x ∂gaussian d,x ∈ S ↔ x ∈ T) :
    gaussianBVPerimeter S = gaussianBVPerimeter T := by
  unfold gaussianBVPerimeter
  congr 1
  funext X
  congr 1
  rw [← integral_indicator hS,← integral_indicator hT]
  apply integral_congr_ae
  filter_upwards [hST] with x hx
  by_cases hs : x ∈ S
  · simp [hs,hx.mp hs]
  · have ht : x ∉ T := fun ht => hs (hx.mpr ht)
    simp [hs,ht]

end GaussianMeasureBridge
